import torch
import torch.nn as nn
import torch.nn.functional as F
import sympy as sp


class SumOfRelu(nn.Module):
    def __init__(self, n_in, n_out=1, n_summands=2, input_vars=None):
        super(SumOfRelu, self).__init__()

        self.n_summands = n_summands
        self.n_in = n_in
        self.n_out = n_out
        
        if input_vars is not None:
            self.input_vars = input_vars

        self.fc1 = nn.Linear(n_in, n_summands*n_out, bias=False)
        self.out = []
        for i in range(0, n_out):
            row = torch.ones(n_summands)
            for j in range(0, i):
                row = torch.cat((torch.zeros(n_summands), row), 0)
            for j in range(i+1, n_out):
                row = torch.cat((row, torch.zeros(n_summands)), 0)
            self.out.append(row)

        self.out = torch.stack(self.out, dim=0)

    def forward(self, state):
        layer = self.fc1(state)
        layer = F.relu(layer)
        layer = F.linear(layer, self.out)
        return layer
        
    def get_weights(self):
        return [self.fc1.weight.data.numpy()]

    def get_round_weights(self):
        return self.fc1.weight.data.numpy().round()
        
    def sympy_expr(self):
        relu = sp.Function('relu')

        expr = sp.Matrix(sp.symbols(self.input_vars, real=True))
        expr1 = self.fc1.weight.data.numpy() * expr
        expr1 = expr1.applyfunc(relu)
        return expr1

    def sympy_rounded_expr(self):
        relu = sp.Function('relu')

        expr = sp.Matrix(sp.symbols(self.input_vars, real=True))
        expr1 = self.fc1.weight.data.numpy().round() * expr
        expr1 = expr1.applyfunc(relu)
        return expr1

    def print_sympy(self):
        expr1 = self.sympy_expr()

        for e in expr1:
            print(e)
        print("After rounding:")

        expr = self.sympy_rounded_expr()
        for e in expr:
            print(e)
