import torch
import torch.nn as nn
import torch.nn.functional as F
import sympy as sp
import numpy as np


class TwoLayerRelu(nn.Module):
    def __init__(self, n_in, n_summands=10, input_vars=None):
        super(TwoLayerRelu, self).__init__()

        self.n_summands = n_summands
        self.n_in = n_in

        if input_vars is not None:
            self.input_vars = input_vars

        self.fc1 = nn.Linear(n_in, n_summands, bias=False)
        self.fc2 = nn.Linear(n_summands, 1, bias=False)

    def forward(self, state):
        layer = self.fc1(state)  # first layer
        layer = F.relu(layer)
        layer = self.fc2(layer)  # second layer
        layer = F.relu(layer)
        return layer

    def get_weights(self):
        return [self.fc1.weight.data.numpy(), self.fc2.weight.data.numpy()]

    def get_round_weights(self):
        return [self.fc1.weight.data.numpy().round(), self.fc2.weight.data.numpy().round()]

    def sympy_expr(self):
        relu = sp.Function('relu')

        expr = sp.Matrix(sp.symbols(self.input_vars, real=True))
        expr1 = self.fc1.weight.data.numpy() * expr
        expr1 = expr1.applyfunc(relu)

        expr2 = self.fc2.weight.data.numpy() * expr1  # Todo check if this is correct
        expr2 = expr2.applyfunc(relu)

        return expr2

    def sympy_rounded_expr(self):
        relu = sp.Function('relu')

        expr = sp.Matrix(sp.symbols(self.input_vars, real=True))
        expr1 = self.fc1.weight.data.numpy().round() * expr
        expr1 = expr1.applyfunc(relu)

        expr2 = self.fc2.weight.data.numpy().round() * expr1  # Todo check if this is correct
        expr2 = expr2.applyfunc(relu)

        return expr2

    def print_sympy(self):
        expr1 = self.sympy_expr()

        for e in expr1:
            print(e)
        print("After rounding:")

        expr = self.sympy_rounded_expr()
        for e in expr:
            print(e)
