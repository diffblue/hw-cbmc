from torch import optim


def simple_learning(trace, loop_head, Model, loss_func, iterations=10000):
    """
    Function for simplest learning algorithm.
    """
    input_before, input_after = trace.get_pairing_of_all_traces_as_tensors(loop_head)
    print("Training data: {} pairs".format(len(input_after)))

    input_dim = len(trace.get_pos_identifiers())
    input_vars = trace.get_pos_identifiers(frame=5)
    
    # creating model with info from trace
    model = Model(input_dim, input_vars=input_vars)

    # Learning
    optimiser = optim.AdamW(model.parameters(), lr=.01)
    for t in range(iterations):
        optimiser.zero_grad()

        output_before = model(input_before)
        output_after = model(input_after)

        loss = loss_func(output_before, output_after)

        #print(t, "loss:", loss.item())
        if loss == 0.:
            break
        loss.backward()
        optimiser.step()

    return model, loss.item()
