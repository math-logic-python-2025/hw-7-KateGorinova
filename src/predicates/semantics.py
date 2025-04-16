# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/semantics.py

"""Semantic analysis of predicate-logic expressions."""

from typing import FrozenSet, Generic, TypeVar

from src.logic_utils import frozendict

from src.predicates.syntax import *

#: A generic type for a universe element in a model.
T = TypeVar("T")


@frozen
class Model(Generic[T]):
    """An immutable model for predicate-logic constructs.

    Attributes:
        universe (`~typing.FrozenSet`\\[`T`]): the set of elements to which
            terms can be evaluated and over which quantifications are defined.
        constant_interpretations (`~typing.Mapping`\\[`str`, `T`]): mapping from
            each constant name to the universe element to which it evaluates.
        relation_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each relation name to its arity, or to ``-1`` if the relation is the
            empty relation.
        relation_interpretations (`~typing.Mapping`\\[`str`, `~typing.AbstractSet`\\[`~typing.Tuple`\\[`T`, ...]]]):
            mapping from each n-ary relation name to argument n-tuples (of
            universe elements) for which the relation is true.
        function_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each function name to its arity.
        function_interpretations (`~typing.Mapping`\\[`str`, `~typing.Mapping`\\[`~typing.Tuple`\\[`T`, ...], `T`]]):
            mapping from each n-ary function name to the mapping from each
            argument n-tuple (of universe elements) to the universe element that
            the function outputs given these arguments.
    """

    universe: FrozenSet[T]
    constant_interpretations: Mapping[str, T]
    relation_arities: Mapping[str, int]
    relation_interpretations: Mapping[str, AbstractSet[Tuple[T, ...]]]
    function_arities: Mapping[str, int]
    function_interpretations: Mapping[str, Mapping[Tuple[T, ...], T]]

    def __init__(
        self,
        universe: AbstractSet[T],
        constant_interpretations: Mapping[str, T],
        relation_interpretations: Mapping[str, AbstractSet[Tuple[T, ...]]],
        function_interpretations: Mapping[str, Mapping[Tuple[T, ...], T]] = frozendict(),
    ):
        """Initializes a `Model` from its universe and constant, relation, and
        function name interpretations.

        Parameters:
            universe: the set of elements to which terms are to be evaluated
                and over which quantifications are to be defined.
            constant_interpretations: mapping from each constant name to a
                universe element to which it is to be evaluated.
            relation_interpretations: mapping from each relation name that is to
                be the name of an n-ary relation, to the argument n-tuples (of
                universe elements) for which the relation is to be true.
            function_interpretations: mapping from each function name that is to
                be the name of an n-ary function, to a mapping from each
                argument n-tuple (of universe elements) to a universe element
                that the function is to output given these arguments.
        """
        for constant in constant_interpretations:
            assert is_constant(constant)
            assert constant_interpretations[constant] in universe
        relation_arities = {}
        for relation in relation_interpretations:
            assert is_relation(relation)
            relation_interpretation = relation_interpretations[relation]
            if len(relation_interpretation) == 0:
                arity = -1  # any
            else:
                some_arguments = next(iter(relation_interpretation))
                arity = len(some_arguments)
                for arguments in relation_interpretation:
                    assert len(arguments) == arity
                    for argument in arguments:
                        assert argument in universe
            relation_arities[relation] = arity
        function_arities = {}
        for function in function_interpretations:
            assert checking(function)
            function_interpretation = function_interpretations[function]
            assert len(function_interpretation) > 0
            some_argument = next(iter(function_interpretation))
            arity = len(some_argument)
            assert arity > 0
            assert len(function_interpretation) == len(universe) ** arity
            for arguments in function_interpretation:
                assert len(arguments) == arity
                for argument in arguments:
                    assert argument in universe
                assert function_interpretation[arguments] in universe
            function_arities[function] = arity

        self.universe = frozenset(universe)
        self.constant_interpretations = frozendict(constant_interpretations)
        self.relation_arities = frozendict(relation_arities)
        self.relation_interpretations = frozendict(
            {relation: frozenset(relation_interpretations[relation]) for relation in relation_interpretations}
        )
        self.function_arities = frozendict(function_arities)
        self.function_interpretations = frozendict(
            {function: frozendict(function_interpretations[function]) for function in function_interpretations}
        )

    def __repr__(self) -> str:
        """Computes a string representation of the current model.

        Returns:
            A string representation of the current model.
        """
        return (
            "Universe="
            + str(self.universe)
            + "; Constant Interpretations="
            + str(self.constant_interpretations)
            + "; Relation Interpretations="
            + str(self.relation_interpretations)
            + (
                "; Function Interpretations=" + str(self.function_interpretations)
                if len(self.function_interpretations) > 0
                else ""
            )
        )

    def evaluate_term(self, term: Term, assignment: Mapping[str, T] = frozendict()) -> T:
        """Calculates the value of the given term in the current model under the
        given assignment of values to variable names.

        Parameters:
            term: term to calculate the value of, for the constant and function
                names of which the current model has interpretations.
            assignment: mapping from each variable name in the given term to a
                universe element to which it is to be evaluated.

        Returns:
            The value (in the universe of the current model) of the given
            term in the current model under the given assignment of values to
            variable names.
        """
        assert term.constants().issubset(self.constant_interpretations.keys())
        assert term.variables().issubset(assignment.keys())
        for function, arity in term.functions():
            assert function in self.function_interpretations and self.function_arities[function] == arity

        root_value = term.root
        if is_constant(root_value):
            evaluated_result = self.constant_interpretations.get(root_value)
        elif is_variable(root_value):
            evaluated_result = assignment.get(root_value)
        elif checking(root_value):
            args_evaluated = [self.evaluate_term(arg, assignment) for arg in term.arguments]
            func_interp = self.function_interpretations.get(root_value, {})
            evaluated_result = func_interp.get(tuple(args_evaluated))
        return evaluated_result

        # Task 7.7

    def evaluate_formula(self, formula: Formula, assignment: Mapping[str, T] = frozendict()) -> bool:
        """Calculates the truth value of the given formula in the current model
        under the given assignment of values to free occurrences of variable
        names.

        Parameters:
            formula: formula to calculate the truth value of, for the constant,
                function, and relation names of which the current model has
                interpretations.
            assignment: mapping from each variable name that has a free
                occurrence in the given formula to a universe element to which
                it is to be evaluated.

        Returns:
            The truth value of the given formula in the current model under the
            given assignment of values to free occurrences of variable names.
        """
        assert formula.constants().issubset(self.constant_interpretations.keys())
        assert formula.free_variables().issubset(assignment.keys())
        for function, arity in formula.functions():
            assert function in self.function_interpretations and self.function_arities[function] == arity
        for relation, arity in formula.relations():
            assert relation in self.relation_interpretations and self.relation_arities[relation] in {-1, arity}

        operator = formula.root

        if is_equality(operator):
            left_val = self.evaluate_term(formula.arguments[0], assignment)
            right_val = self.evaluate_term(formula.arguments[1], assignment)
            return left_val is right_val

        elif is_relation(operator):
            evaluated_args = [self.evaluate_term(arg, assignment) for arg in formula.arguments]
            return tuple(evaluated_args) in self.relation_interpretations[operator]

        elif is_unary(operator):
            inner_result = self.evaluate_formula(formula.first, assignment)
            return not inner_result

        elif is_binary(operator):
            left_expr = self.evaluate_formula(formula.first, assignment)
            right_expr = self.evaluate_formula(formula.second, assignment)

            binary_operations = {
                '&': lambda x, y: x and y,
                '|': lambda x, y: x or y,
                '->': lambda x, y: not x or y,
                '-&': lambda x, y: not (x and y),
                '-|': lambda x, y: not (x or y),
                '+': lambda x, y: x != y,
                '<->': lambda x, y: x == y
            }

            if operator in binary_operations:
                return binary_operations[operator](left_expr, right_expr)

        elif is_quantifier(operator):
            var_name = formula.variable
            possible_values = ({var_name: val} for val in self.universe)

            results = []
            for val_assignment in possible_values:
                combined_assignment = {**assignment, **val_assignment}
                res = self.evaluate_formula(formula.statement, combined_assignment)
                results.append(res)

            if operator == 'A':
                return all(results)
            else:
                return any(results)

        return False
        # Task 7.8

    def is_model_of(self, formulas: AbstractSet[Formula]) -> bool:
        """Checks if the current model is a model of the given formulas.

        Parameters:
            formulas: formulas to check, for the constant, function, and
                relation names of which the current model has interpretations.

        Returns:
            ``True`` if each of the given formulas evaluates to true in the
            current model under any assignment of elements from the universe of
            the current model to the free occurrences of variable names in that
            formula, ``False`` otherwise.
        """
        for formula in formulas:
            assert formula.constants().issubset(self.constant_interpretations.keys())
            for function, arity in formula.functions():
                assert function in self.function_interpretations and self.function_arities[function] == arity
            for relation, arity in formula.relations():
                assert relation in self.relation_interpretations and self.relation_arities[relation] in {-1, arity}
            modified_formulas = set()
            for current_formula in formulas:
                updated_formula = current_formula
                for var in updated_formula.free_variables():
                    updated_formula = Formula('A', var, updated_formula)
                modified_formulas.add(updated_formula)
            return all(self.evaluate_formula(f) for f in modified_formulas)
        # Task 7.9
