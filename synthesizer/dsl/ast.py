from enum import Enum, unique

from lark import ast_utils


class AstException(Exception):
    pass


@unique
class BinaryOperator(Enum):
    PLUS = 1
    MINUS = 2
    TIMES = 3
    DIV = 4
    MODULO = 5
    EQUALS = 6

    GREATER = 7
    GREATER_EQ = 8
    LESSTHAN = 9
    LESSTHAN_EQ = 10
    AND = 11
    OR = 12
    NOTEQUALS = 13


@unique
class UnaryOperator(Enum):
    NOT = 1
    LEN = 2
    NEG = 3
    ABS = 4


class Node(ast_utils.Ast):
    pass


class Expression(Node):
    pass


__builtin__names__ = ["list", "id"]


class Variable(Expression):
    """
    A Variable is a named entity.
    """

    def __init__(self, name: str, declaring_builtin=False) -> None:
        if not declaring_builtin and name in __builtin__names__:
            raise AstException(
                f"cannot redeclare builtin {name}, use the predeclared builtin instead"
            )
        self.name = name


builtins = {
    "list": Variable("list", declaring_builtin=True),
    "id": Variable("id", declaring_builtin=True)
}


class Constant(Expression):
    pass


class UnExpr(Expression):
    pass


class BinExpr(Expression):
    pass


class IndexExpr(Expression):
    pass


class TernExpr(Expression):
    pass


class ListExpr(Expression):
    pass


class DictExpr(Expression):
    pass


class Instruction(Node):
    pass


class ApiCallBinding(Instruction):
    pass


class DataTransformation(Instruction):
    pass


class IfThenElse(Instruction):
    pass


class Return(Instruction):
    pass


class RetryUntil(Instruction):
    pass


class Block(Node):
    pass


class FunctionDecl(Node):
    pass


class SyntDecl(Node):
    pass


class Program(Node):
    pass
