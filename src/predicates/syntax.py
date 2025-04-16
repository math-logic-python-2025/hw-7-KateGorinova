# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from src.logic_utils import (
    frozen,
    memoized_parameterless_method,
)

from src.propositions.syntax import (
    Formula as PropositionalFormula,
)


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """

    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (
        ((string[0] >= "0" and string[0] <= "9") or (string[0] >= "a" and string[0] <= "e")) and string.isalnum()
    ) or string == "_"


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= "u" and string[0] <= "z" and string.isalnum()



def checking(string: str) -> bool:
    return string[0] >= "f" and string[0] <= "t" and string.isalnum()


def sbf(string: str) -> Tuple:
    if (open_bracket := string[0]) not in {'[','('}:
        print(f"{string} doesn't start with a bracket")
        return string
    if open_bracket == '[':
        close_bracket =']'
    else:
        close_bracket = ')'
    counter = 0
    for i,j in enumerate(string):
        if j == open_bracket:
            counter +=1
        elif j == close_bracket:
            counter -=1
        if counter == 0:
            return string[:i+1], string[i+1:]

def so(string: str) -> list:
    if string[0] in {'&', '|', '+'}:
        return string[0], string[1:]
    elif string[0] == '-':
        assert string[1] in {'>','&','|'}
        return string[0:2], string[2:]
    else:
        assert string[0:3] == '<->'
        return string[0:3], string[3:]

def st(string: str) -> Tuple:
    assert string
    sample = string[0]
    if sample == '_':
        return ('_', string[1:])
    counter = 0
    while counter < len(string) and string[counter].isalnum():
        counter += 1
    if is_constant(sample) or is_variable(sample):
        return string[:counter], string[counter:]

    elif checking(sample):
        arguments, suffix = sbf(string[counter:])
        return string[:counter]+arguments, suffix

def sforn(string: str) -> Tuple:
    assert string
    counter = 0
    while string[counter].isalnum():
        counter += 1
    return string[:counter], *sbf(string[counter:])

@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a function name.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments for the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert checking(root)
            assert arguments is not None and len(arguments) > 0
            self.root = root
            self.arguments = tuple(arguments)

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        current_root = self.root
        if is_variable(current_root) or is_constant(current_root):
            result = current_root
        else:
            if type(self) in (Term, Formula):
                args_str = ",".join([arg.__repr__() for arg in self.arguments])
                result = f'{current_root}({args_str})'
            else:
                raise TypeError("Unexpected type")
        return result
        # Task 7.1

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """

        def sbf(string: str) -> Tuple:
            if (open_bracket := string[0]) not in {'[', '('}:
                print(f"{string} doesn't start with a bracket")
                return string
            if open_bracket == '[':
                close_bracket = ']'
            else:
                close_bracket = ')'
            counter = 0
            for i, j in enumerate(string):
                if j == open_bracket:
                    counter += 1
                elif j == close_bracket:
                    counter -= 1
                if counter == 0:
                    return string[:i + 1], string[i + 1:]

        def extract_function_components(string: str) -> Tuple:
            assert string
            counter = 0
            while string[counter].isalnum():
                counter += 1
            return string[:counter], *sbf(string[counter:])

        def split_components(string: str) -> Tuple:
            assert string
            sample = string[0]
            if sample == '_':
                return ('_', string[1:])
            counter = 0
            while counter < len(string) and string[counter].isalnum():
                counter += 1
            if is_constant(sample) or is_variable(sample):
                return string[:counter], string[counter:]

            elif checking(sample):
                arguments, suffix = sbf(string[counter:])
                return string[:counter] + arguments, suffix

        if not string:
            return None, string

        first_char = string[0]

        if is_constant(first_char) or is_variable(first_char):
            term_part, remaining_str = split_components(string)
            return Term(term_part), remaining_str

        if not checking(first_char):
            raise ValueError("Invalid term structure")

        func_name, arguments, rest = extract_function_components(string)
        args_content = arguments[1:-1]
        parsed_args = []

        while args_content:
            current_arg, args_content = split_components(args_content)
            parsed_args.append(current_arg)

            if args_content and args_content[0] == ',':
                args_content = args_content[1:].lstrip()

        processed_args = [Term._parse_prefix(arg)[0] for arg in parsed_args]
        return Term(func_name, processed_args), rest

        # Task 7.3a

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        term = Term._parse_prefix(string)[0]
        return term
        # Task 7.3b

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        node = self.root
        if is_constant(node):
            return {node}

        if is_variable(node):
            return set()

        if checking(node):
            found_constants = set()
            for arg in self.arguments:
                found_constants.update(Term.constants(arg))
            return found_constants
        # Harris J. Bolus - Task 7.5a

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        current_root = self.root
        if is_variable(current_root):
            return {current_root}

        if is_constant(current_root):
            return set()

        if checking(current_root):
            found_vars = set()
            for arg in self.arguments:
                found_vars.update(Term.variables(arg))
            return found_vars
        # Harris J. Bolus - Task 7.5b

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        current_root = self.root
        function_set = set()

        if checking(current_root):
            function_set.add((current_root, len(self.arguments)))

            for arg in self.arguments:
                function_set.update(arg.functions())

        return function_set
        # Task 7.5c

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Term:
        """Substitutes in the current term, each constant name `construct` or
        variable name `construct` that is a key in `substitution_map` with the
        term `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current term are substituted (i.e., those originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from
                `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1


@lru_cache(maxsize=100)  # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == "="


@lru_cache(maxsize=100)  # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= "F" and string[0] <= "T" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == "~"


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == "&" or string == "|" or string == "->"


@lru_cache(maxsize=100)  # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == "A" or string == "E"


@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        statement (`~typing.Optional`\\[`Formula`]): the statement quantified by
            the root, if the root is a quantification.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    statement: Optional[Formula]

    def __init__(
        self,
        root: str,
        arguments_or_first_or_variable: Union[Sequence[Term], Formula, str],
        second_or_statement: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable name and statement.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments for the root, if the
                root is a relation name or the equality relation; the first
                operand for the root, if the root is a unary or binary operator;
                the variable name to be quantified by the root, if the root is a
                quantification.
            second_or_statement: the second operand for the root, if the root is
                a binary operator; the statement to be quantified by the root,
                if the root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert isinstance(arguments_or_first_or_variable, Sequence) and not isinstance(
                arguments_or_first_or_variable, str
            )
            if is_equality(root):
                assert len(arguments_or_first_or_variable) == 2
            assert second_or_statement is None
            self.root, self.arguments = root, tuple(arguments_or_first_or_variable)
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is not None
            self.root, self.first, self.second = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.statement
            assert isinstance(arguments_or_first_or_variable, str) and is_variable(arguments_or_first_or_variable)
            assert second_or_statement is not None
            self.root, self.variable, self.statement = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        operator = self.root

        if is_equality(operator):
            left_arg = self.arguments[0].__repr__()
            right_arg = self.arguments[1].__repr__()
            return f'{left_arg}{operator}{right_arg}'

        elif is_relation(operator):
            args_repr = [arg.__repr__() for arg in self.arguments]
            joined_args = ",".join(args_repr)
            return f'{operator}({joined_args})'

        elif is_unary(operator):
            operand_repr = self.first.__repr__()
            return f'{operator}{operand_repr}'

        elif is_binary(operator):
            left_repr = self.first.__repr__()
            right_repr = self.second.__repr__()
            return f'({left_repr}{operator}{right_repr})'

        elif is_quantifier(operator):
            var_repr = self.variable
            stmt_repr = self.statement.__repr__()
            return f'{operator}{var_repr}[{stmt_repr}]'

        else:
            raise ValueError(f"Unknown operator type: {operator}")
    # Task 7.2

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'f(y)=c12'``) or by a variable
            name (e.g., ``'f(y)=x12'``), then the parsed prefix will include
            that entire name (and not just a part of it, such as ``'f(y)=x1'``).
        """
        initial_char = string[0]

        if is_constant(initial_char) or is_variable(initial_char) or checking(initial_char):
            left_part, remaining = st(string)
            assert remaining[0] == '='
            right_part, remaining = st(remaining[1:])
            parsed_left = Term.parse(left_part)
            parsed_right = Term.parse(right_part)
            result = Formula('=', [parsed_left, parsed_right])

        elif is_relation(initial_char):
            name, arguments_part, remaining = sforn(string)
            arguments_str = arguments_part[1:-1]
            arguments = []

            while arguments_str:
                current_arg, arguments_str = st(arguments_str)
                arguments.append(current_arg)
                if arguments_str and arguments_str[0] == ',':
                    arguments_str = arguments_str[1:]
            parsed_arguments = [Term._parse_prefix(arg)[0] for arg in arguments]
            result = Formula(name, parsed_arguments)

        elif is_unary(initial_char):
            inner_formula, remaining = Formula._parse_prefix(string[1:])
            result = Formula('~', inner_formula)

        elif is_quantifier(initial_char):
            quantifier_type = initial_char
            var_name, remaining = st(string[1:])
            inner_expr, remaining = sbf(remaining)
            parsed_inner = Formula._parse_prefix(inner_expr[1:-1])[0]
            result = Formula(quantifier_type, var_name, parsed_inner)

        else:
            assert initial_char == '('
            full_expr, remaining = sbf(string)
            left_expr, rest = Formula._parse_prefix(full_expr[1:])
            op_symbol, right_part = so(rest)
            right_expr = Formula._parse_prefix(right_part)[0]
            result = Formula(op_symbol, left_expr, right_expr)

        return result, remaining
        # Task 7.4a

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        formula = Formula._parse_prefix(string)[0]
        return formula
        # Task 7.4b

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        current_root = self.root
        if is_quantifier(current_root):
            return Formula.constants(self.statement)
        elif is_unary(current_root):
            return Formula.constants(self.first)
        elif is_binary(current_root):
            first_part = Formula.constants(self.first)
            second_part = Formula.constants(self.second)
            return first_part.union(second_part)
        elif is_equality(current_root) or is_relation(current_root):
            found_constants = set()
            for arg in self.arguments:
                arg_constants = Term.constants(arg)
                found_constants = found_constants.union(arg_constants)
            return found_constants
        # Task 7.6a

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        current_root = self.root
        if is_quantifier(current_root):
            first_part = Formula.variables(self.statement)
            second_part = {self.variable}
            return first_part.union(second_part)
        elif is_unary(current_root):
            return Formula.variables(self.first)
        elif is_binary(current_root):
            first_part = Formula.variables(self.first)
            second_part = Formula.variables(self.second)
            return first_part.union(second_part)
        elif is_equality(current_root) or is_relation(current_root):
            found_variables = set()
            for arg in self.arguments:
                arg_variables = Term.variables(arg)
                found_variables = found_variables.union(arg_variables)
            return found_variables
        # Task 7.6b

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        current_root = self.root
        if is_quantifier(current_root):
            free_variables = Formula.free_variables(self.statement) - {self.variable}
            return free_variables
        elif is_unary(current_root):
            return Formula.free_variables(self.first)
        elif is_binary(current_root):
            first_part = Formula.free_variables(self.first)
            second_part = Formula.free_variables(self.second)
            return first_part.union(second_part)
        elif is_equality(current_root) or is_relation(current_root):
            free_variables = set()
            for arg in self.arguments:
                arg_variables = Term.variables(arg)
                free_variables = free_variables.union(arg_variables)
            return free_variables
        # Task 7.6c

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        current_root = self.root
        if is_quantifier(current_root):
            return Formula.functions(self.statement)
        elif is_unary(current_root):
            return Formula.functions(self.first)
        elif is_binary(current_root):
            first_part = Formula.functions(self.first)
            second_part = Formula.functions(self.second)
            return first_part.union(second_part)
        elif is_equality(current_root) or is_relation(current_root):
            functions = set()
            for arg in self.arguments:
                arg_functions = Term.functions(arg)
                functions = functions.union(arg_functions)
            return functions
        # Task 7.6d

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        current_root = self.root
        if is_relation(current_root):
            return {(current_root, len(self.arguments))}
        elif is_quantifier(current_root):
            return Formula.relations(self.statement)
        elif is_unary(current_root):
            return Formula.relations(self.first)
        elif is_binary(current_root):
            first_part = Formula.relations(self.first)
            second_part = Formula.relations(self.second)
            return first_part.union(second_part)
        return set()
        # Task 7.6e

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Formula:
        """Substitutes in the current formula, each constant name `construct` or
        free occurrence of variable name `construct` that is a key in
        `substitution_map` with the term
        `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current formula are substituted (i.e., those originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from `forbidden_variables`
                or a variable name occurrence that becomes bound when that term
                is substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

    def propositional_skeleton(
        self,
    ) -> Tuple[PropositionalFormula, Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation name, equality, or quantifier at its
            root with a propositional variable name, consistently such that
            multiple identical such (outermost) subformulas are substituted with
            the same propositional variable name. The propositional variable
            names used for substitution are obtained, from left to right
            (considering their first occurrence), by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each propositional
            variable name to the subformula for which it was substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(~Q(y)->x=7))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(~z3->z2)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(~z6->z5)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula, substitution_map: Mapping[str, Formula]) -> Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each propositional variable name of
                the given propositional skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each propositional variable name with the
            formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(~z3->z2))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))

            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z9&z2)|(~z3->z2))'),
            ...     {'z2': Formula.parse('x=7'), 'z3': Formula.parse('Q(y)'),
            ...      'z9': Formula.parse('Ax[x=7]')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
