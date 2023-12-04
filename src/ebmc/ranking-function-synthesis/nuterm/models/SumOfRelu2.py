import torch
import torch.nn as nn
import torch.nn.functional as F
import sympy as sp


class SumOfRelu2(nn.Module):
    def __init__(self, n_in, n_out=1, n_summands=2, bias=True, trainable_out=False):
        super(SumOfRelu2, self).__init__()

        self.n_summands = n_summands
        self.n_in = n_in
        self.n_out = n_out
        
        self.fc1 = []
        self.fc2 = []
        for i in range(0, self.n_out):
            hidden = nn.Linear(n_in, n_summands, bias=bias)
            output = nn.Linear(n_summands, 1, bias=False)
            self.register_parameter("hidden"+str(i), hidden.weight)
            if hidden.bias is not None:
                self.register_parameter("bias"+str(i), hidden.bias)

            if trainable_out:
                self.register_parameter("out"+str(i), output.weight)
            else:
                nn.init.constant_(output.weight, 1.)


            self.fc1.append(hidden)
            self.fc2.append(output)
            
    def forward(self, state):
        res = []
        for i in range(0, self.n_out):
            layer = self.fc1[i](state)
            layer = F.relu(layer)
            layer = self.fc2[i](layer)
            res.append(layer)
        return res
