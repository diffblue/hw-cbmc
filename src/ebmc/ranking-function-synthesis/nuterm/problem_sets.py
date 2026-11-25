from strategies import  *

# ===================================
# - experiments
# ===================================
aprove_09_programs = [
    # ===================================
    # - single loop linear
    # ===================================
    ('termination-suite/Aprove_09/GCD5/GCD5.jar', 'GCD5', 'gcd', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/LogBuiltIn/LogBuiltIn.jar', 'LogBuiltIn', 'log', anticorr_sumofrelu2),
    # ('termination-suite/Aprove_09/McCarthyIterative/McCarthyIterative.jar', 'McCarthyIterative', 'loop', anticorr_sumofrelu2), slow
    ('termination-suite/Aprove_09/MinusBuiltIn/MinusBuiltIn.jar', 'MinusBuiltIn', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaA4/PastaA4.jar', 'PastaA4', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaA5/PastaA5.jar', 'PastaA5', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaA6/PastaA6.jar', 'PastaA6', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaA7/PastaA7.jar', 'PastaA7', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB2/PastaB2.jar', 'PastaB2', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB6/PastaB6.jar', 'PastaB6', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB7/PastaB7.jar', 'PastaB7', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB10/PastaB10.jar', 'PastaB10', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB11/PastaB11.jar', 'PastaB11', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB1/PastaB1.jar', 'PastaB1', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB5/PastaB5.jar', 'PastaB5', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaA9/PastaA9.jar', 'PastaA9', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/CountUpRound/CountUpRound.jar', 'CountUpRound', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/DivMinus/DivMinus.jar', 'DivMinus', 'div', anticorr_sumofrelu2),

    # -- supporting invar
    ('termination-suite/Aprove_09/PastaB8/PastaB8.jar', 'PastaB8', 'loop', anticorr_sumofrelu2),
    # needs invariant x >= 0, while precondition imposes x > 0

    # -- nondeterminism; We do not support this
    # ('termination-suite/Aprove_09/PastaC9/PastaC9.jar', 'PastaC9', 'loop', None),
    # ('termination-suite/Aprove_09/PastaC10/PastaC10.jar', 'PastaC10', 'loop', None),
    # ('termination-suite/Aprove_09/PastaC11/PastaC11.jar', 'PastaC11', 'loop', None),

    # ===================================
    # - two loops linear lexicographic
    # ===================================
    ('termination-suite/Aprove_09/PastaA1/PastaA1.jar', 'PastaA1', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB16/PastaB16.jar', 'PastaB16', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB17/PastaB17.jar', 'PastaB17', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaC1/PastaC1.jar', 'PastaC1', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaC2/PastaC2.jar', 'PastaC2', 'loop', anticorr_sumofrelu2),

    # -- supporting invar
    ('termination-suite/Aprove_09/PastaB18/PastaB18.jar', 'PastaB18', 'loop', anticorr_sumofrelu2),

    # ===================================
    # - single loop non-linear
    # ===================================
    ('termination-suite/Aprove_09/PastaB12/PastaB12.jar', 'PastaB12', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB13/PastaB13.jar', 'PastaB13', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaA10/PastaA10.jar', 'PastaA10', 'loop', anticorr_sumofrelu2),  # abs(x - y)
    ('termination-suite/Aprove_09/PastaC3/PastaC3.jar', 'PastaC3', 'loop', anticorr_sumofrelu2),
    # A solution is y - min{x,z}, or Relu(y-x) + Relu (y-z)
    ('termination-suite/Aprove_09/LogIterative/LogIterative.jar', 'LogIterative', 'log', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/LogMult/LogMult.jar', 'LogMult', 'log', anticorr_sumofrelu2),
    
    # -- supporting invar
    ('termination-suite/Aprove_09/PastaC5/PastaC5.jar', 'PastaC5', 'loop', anticorr_sumofrelu2),

    # ===================================
    # - unknown strategy
    # ===================================
    ('termination-suite/Aprove_09/Round3/Round3.jar', 'Round3', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB14/PastaB14.jar', 'PastaB14', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB15/PastaB15.jar', 'PastaB15', 'loop', anticorr_sumofrelu2),

    # ===================================
    # - Pathological cases (Drawbacks discussed in submitted paper)
    # ===================================
    # argument changes at each iteration
    ('termination-suite/Aprove_09/PlusSwap/PlusSwap.jar', 'PlusSwap', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PlusSwapUnroll2/PlusSwapUnroll2.jar', 'PlusSwapUnroll2', 'loop', anticorr_sumofrelu2),
    # This loop executes exactly once. the while can basically be replaced by if (x > y) and it does a swap.
    ('termination-suite/Aprove_09/PastaB4/PastaB4.jar', 'PastaB4', 'loop', anticorr_sumofrelu2),
    # Maybe we require an invariant or something. I think the ranking function is close to k - j but it gets interupted by the first loop condition when j is >=100
    ('termination-suite/Aprove_09/PastaC7/PastaC7.jar', 'PastaC7', 'loop', anticorr_sumofrelu2),
    ('termination-suite/Aprove_09/PastaB3/PastaB3.jar', 'PastaB3', 'loop', anticorr_sumofrelu2),  # one iteration only
    # - model not expressive enough
    # Usually the trace is simply too short, i.e. 3/4 long
]


sv_comp_termination = [
    #working
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-speedpldi4/AliasDarteFeautrierGonnordSAS2010speedpldi4.jar', 'AliasDarteFeautrierGonnordSAS2010speedpldi4', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-easy1/ChawdharyCookGulwaniSagivYangESOP2008easy1.jar', 'ChawdharyCookGulwaniSagivYangESOP2008easy1', "loop", i40_rank),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-easy1/AliasDarteFeautrierGonnordSAS2010easy1.jar', 'AliasDarteFeautrierGonnordSAS2010easy1', "loop", i40_rank), # This is the same program as ChawdharyCookGulwaniSagivYangESOP2008easy1
    ('termination-suite/termination-crafted-lit/terminating/BradleyMannaSipma-CAV2005-Fig1/BradleyMannaSipmaCAV2005Fig1.jar', 'BradleyMannaSipmaCAV2005Fig1', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/LeikeHeizmann-TACAS2014-Ex7/LeikeHeizmannTACAS2014Ex7.jar', 'LeikeHeizmannTACAS2014Ex7', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-easy2-1/AliasDarteFeautrierGonnordSAS2010easy21.jar', 'AliasDarteFeautrierGonnordSAS2010easy21', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.10/ChenFlurMukhopadhyaySAS2012Ex210.jar', 'ChenFlurMukhopadhyaySAS2012Ex210', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.08/ChenFlurMukhopadhyaySAS2012Ex308.jar', 'ChenFlurMukhopadhyaySAS2012Ex308', "loop", anticorr_sumofrelu), # This is probably gonna stay hard
    ('termination-suite/termination-crafted-lit/terminating/aviad/Aviad.jar', 'Aviad', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-ndecr/AliasDarteFeautrierGonnordSAS2010ndecr.jar', 'AliasDarteFeautrierGonnordSAS2010ndecr', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/GulavaniGulwani-CAV2008-Fig1c/GulavaniGulwaniCAV2008Fig1c.jar', 'GulavaniGulwaniCAV2008Fig1c', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig8/HeizmannHoenickeLeikePodelskiATVA2013Fig8.jar', 'HeizmannHoenickeLeikePodelskiATVA2013Fig8', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/CookSeeZuleger-TACAS2013-Fig8a-modified/CookSeeZulegerTACAS2013Fig8amodified.jar', 'CookSeeZulegerTACAS2013Fig8amodified', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/CookSeeZuleger-TACAS2013-Fig8a/CookSeeZulegerTACAS2013Fig8a.jar', 'CookSeeZulegerTACAS2013Fig8a', "loop", anticorr_sumofrelu),
    #('termination-suite/termination-crafted-lit/terminating/genady/Genady.jar', 'Genady', "loop", genady_test), genady_test not found
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig9/HeizmannHoenickeLeikePodelskiATVA2013Fig9.jar', 'HeizmannHoenickeLeikePodelskiATVA2013Fig9', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.19/ChenFlurMukhopadhyaySAS2012Ex219.jar', 'ChenFlurMukhopadhyaySAS2012Ex219', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.07/ChenFlurMukhopadhyaySAS2012Ex207.jar','ChenFlurMukhopadhyaySAS2012Ex207', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/LeikeHeizmannWST2014Ex9/LeikeHeizmannWST2014Ex9.jar', 'LeikeHeizmannWST2014Ex9', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-easy2/ChawdharyCookGulwaniSagivYangESOP2008easy2.jar','ChawdharyCookGulwaniSagivYangESOP2008easy2', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/LeikeHeizmann-TACAS2014-Ex1/LeikeHeizmannTACAS2014Ex1.jar','LeikeHeizmannTACAS2014Ex1', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig4/HeizmannHoenickeLeikePodelskiATVA2013Fig4.jar','HeizmannHoenickeLeikePodelskiATVA2013Fig4', "loop", None), #TODO Exception with mvgaussian
    ('termination-suite/termination-crafted-lit/terminating/LeikeHeizmann-TACAS2014-Ex9/LeikeHeizmannTACAS2014Ex9.jar','LeikeHeizmannTACAS2014Ex9', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-wise/AliasDarteFeautrierGonnordSAS2010wise.jar','AliasDarteFeautrierGonnordSAS2010wise', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-easy2-2/AliasDarteFeautrierGonnordSAS2010easy22.jar','AliasDarteFeautrierGonnordSAS2010easy22', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.13/ChenFlurMukhopadhyaySAS2012Ex213.jar','ChenFlurMukhopadhyaySAS2012Ex213', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig5-modified/HeizmannHoenickeLeikePodelskiATVA2013Fig5modified.jar', 'HeizmannHoenickeLeikePodelskiATVA2013Fig5modified', "loop", anticorr_sumofrelu), # TODO check if this is a bug
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.01/ChenFlurMukhopadhyaySAS2012Ex301.jar', 'ChenFlurMukhopadhyaySAS2012Ex301', "loop", anticorr_sumofrelu),
    (
    'termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.16/ChenFlurMukhopadhyaySAS2012Ex216.jar',
    'ChenFlurMukhopadhyaySAS2012Ex216', "loop", anticorr_sumofrelu),

    # ##########################
    #  Does not check correctly
    # ##########################
    #  We learn relu(x), relu(y), relu(x+y), relu(x - y) and the checker rejects all of them. But it should accept at least one of them (the first one, probably)
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig1/HeizmannHoenickeLeikePodelskiATVA2013Fig1.jar', 'HeizmannHoenickeLeikePodelskiATVA2013Fig1', "loop", anticorr_sumofrelu),
    # The RF is very easy. But the checker does not accept y even though it is learned
    ('termination-suite/termination-crafted-lit/terminating/PodelskiRybalchenkoTACAS2011Fig2/PodelskiRybalchenkoTACAS2011Fig1.jar','PodelskiRybalchenkoTACAS2011Fig1', "loop", anticorr_sumofrelu),
    # Not sure if we learn the correct function but checking throws an exception either way
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-speedFails4/AliasDarteFeautrierGonnordSAS2010speedFails4.jar','AliasDarteFeautrierGonnordSAS2010speedFails4', "loop", None),
    # Modified version (HeizmannHoenickeLeikePodelski-ATVA2013-Fig5-modified) checks correctly as we add invariant to loop guard
    ( 'termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig5/HeizmannHoenickeLeikePodelskiATVA2013Fig5.jar','HeizmannHoenickeLeikePodelskiATVA2013Fig5', "loop", anticorr_sumofrelu),  # TODO check if this is a bug

    # ##########################
    #  Does not learn correctly
    #  No known technical issues but doesn't work for unknown reasons (maybe pathological case, maybe the RF is to complicated)
    # ##########################
    ('termination-suite/termination-crafted-lit/terminating/NoriSharmaFSE2013Fig7/NoriSharmaFSE2013Fig7.jar','NoriSharmaFSE2013Fig7', "loop", anticorr_sumofrelu),  # TODO Probably easy to fix
    #todo Might be easy, might be pathological. rf might be -x + y, but we learn - x - z note that we have the instructio x = z all the time

    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.10/ChenFlurMukhopadhyaySAS2012Ex310.jar', 'ChenFlurMukhopadhyaySAS2012Ex310', "loop", anticorr_sumofrelu),
    # Probably complex ranking function
    ('termination-suite/termination-crafted-lit/terminating/GopanReps-CAV2006-Fig1a/GopanRepsCAV2006Fig1a.jar','GopanRepsCAV2006Fig1a', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.04/ChenFlurMukhopadhyaySAS2012Ex304.jar','ChenFlurMukhopadhyaySAS2012Ex304', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/Masse-VMCAI2014-Ex6/MasseVMCAI2014Ex6.jar','MasseVMCAI2014Ex6', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.06/ChenFlurMukhopadhyaySAS2012Ex206.jar','ChenFlurMukhopadhyaySAS2012Ex206', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-speedpldi2/AliasDarteFeautrierGonnordSAS2010speedpldi2.jar','AliasDarteFeautrierGonnordSAS2010speedpldi2', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.07/ChenFlurMukhopadhyaySAS2012Ex307.jar','ChenFlurMukhopadhyaySAS2012Ex307', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-speedpldi3/AliasDarteFeautrierGonnordSAS2010speedpldi3.jar','AliasDarteFeautrierGonnordSAS2010speedpldi3', "loop", anticorr_sumofrelu),
    ('termination-suite/terminaNoriSharmaFSE2013Fig7tion-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.08/ChenFlurMukhopadhyaySAS2012Ex208.jar', 'ChenFlurMukhopadhyaySAS2012Ex208', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.21/ChenFlurMukhopadhyaySAS2012Ex221.jar','ChenFlurMukhopadhyaySAS2012Ex221', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/BrockschmidtCookFuhs-CAV2013-Introduction/BrockschmidtCookFuhsCAV2013Introduction.jar','BrockschmidtCookFuhsCAV2013Introduction', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-terminate/AliasDarteFeautrierGonnordSAS2010terminate.jar','AliasDarteFeautrierGonnordSAS2010terminate', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/PodelskiRybalchenkoVMCAI2004Ex2/PodelskiRybalchenkoVMCAI2004Ex2.jar','PodelskiRybalchenkoVMCAI2004Ex2', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig2/HeizmannHoenickeLeikePodelskiATVA2013Fig2.jar','HeizmannHoenickeLeikePodelskiATVA2013Fig2', "loop", anticorr_sumofrelu),
    # complex, probably with max
    ('termination-suite/termination-crafted-lit/terminating/GulavaniGulwani-CAV2008-Fig1a/GulavaniGulwaniCAV2008Fig1a.jar', 'GulavaniGulwaniCAV2008Fig1a', "loop", anticorr_sumofrelu),
    # anticorr_sumofrelu non linear
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.05/ChenFlurMukhopadhyaySAS2012Ex305.jar', 'ChenFlurMukhopadhyaySAS2012Ex305', "loop", anticorr_sumofrelu),
    # anticorr_sumofrelu non linear
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex4.01/ChenFlurMukhopadhyaySAS2012Ex401.jar', 'ChenFlurMukhopadhyaySAS2012Ex401', "loop", anticorr_sumofrelu),
    #hard
    ('termination-suite/termination-crafted-lit/terminating/KroeningSharyginaTsitovichWintersteiger-CAV2010-Fig1/KroeningSharyginaTsitovichWintersteigerCAV2010Fig1.jar', 'KroeningSharyginaTsitovichWintersteigerCAV2010Fig1', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/CookSeeZuleger-TACAS2013-Fig8b/CookSeeZulegerTACAS2013Fig8b.jar', 'CookSeeZulegerTACAS2013Fig8b', "loop", anticorr_sumofrelu), # Simple program but maybe complex rf
    ('termination-suite/termination-crafted-lit/terminating/Masse-VMCAI2014-Fig1a/MasseVMCAI2014Fig1a.jar', 'MasseVMCAI2014Fig1a', "loop", anticorr_sumofrelu), # rf is probably a but the operations on b make it difficult to learn
    # Complex problem
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-cousot9/AliasDarteFeautrierGonnordSAS2010cousot9.jar', 'AliasDarteFeautrierGonnordSAS2010cousot9', "loop", anticorr_sumofrelu),
     # hard, non-linear
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.03/ChenFlurMukhopadhyaySAS2012Ex303.jar', 'ChenFlurMukhopadhyaySAS2012Ex303', "loop", anticorr_sumofrelu),
    # hard, might be pathological
    ('termination-suite/termination-crafted-lit/terminating/ColonSipma-TACAS2001-Fig1/ColonSipmaTACAS2001Fig1.jar', 'ColonSipmaTACAS2001Fig1', "loop", anticorr_sumofrelu),
    # hard
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Fig1/ChenFlurMukhopadhyaySAS2012Fig1.jar', 'ChenFlurMukhopadhyaySAS2012Fig1', "loop", anticorr_sumofrelu),
    # No idea, probably hard
    ('termination-suite/termination-crafted-lit/terminating/NoriSharmaFSE2013Fig8/NoriSharmaFSE2013Fig8.jar', 'NoriSharmaFSE2013Fig8', "loop", anticorr_sumofrelu),
    # No idea, probably hard, non linear
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.18/ChenFlurMukhopadhyaySAS2012Ex218.jar', 'ChenFlurMukhopadhyaySAS2012Ex218', "loop", anticorr_sumofrelu),
    # Hard, probably non-linear
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.09/ChenFlurMukhopadhyaySAS2012Ex209.jar', 'ChenFlurMukhopadhyaySAS2012Ex209', "loop", anticorr_sumofrelu),

    # Nested Loops
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-nestedLoop-2/AliasDarteFeautrierGonnordSAS2010nestedLoop2.jar','AliasDarteFeautrierGonnordSAS2010nestedLoop2', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/LarrazOliverasRodriguez-CarbonellRubio-FMCAD2013-Fig1/LarrazOliverasRodriguezCarbonellRubioFMCAD2013Fig1.jar','LarrazOliverasRodriguezCarbonellRubioFMCAD2013Fig1', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-nestedLoop-1/AliasDarteFeautrierGonnordSAS2010nestedLoop1.jar','AliasDarteFeautrierGonnordSAS2010nestedLoop1', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/Urban-WST2013-Fig2/UrbanWST2013Fig2.jar','UrbanWST2013Fig2', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-wcet2/AliasDarteFeautrierGonnordSAS2010wcet2.jar','AliasDarteFeautrierGonnordSAS2010wcet2', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/BrockschmidtCookFuhs-CAV2013-Fig9a/BrockschmidtCookFuhsCAV2013Fig9a.jar','BrockschmidtCookFuhsCAV2013Fig9a', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-complex/AliasDarteFeautrierGonnordSAS2010complex.jar','AliasDarteFeautrierGonnordSAS2010complex', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-while2/AliasDarteFeautrierGonnordSAS2010while2.jar','AliasDarteFeautrierGonnordSAS2010while2', "loop", anticorr_sumofrelu),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-loops/AliasDarteFeautrierGonnordSAS2010loops.jar','AliasDarteFeautrierGonnordSAS2010loops', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/PodelskiRybalchenkoLICS2004Fig1/PodelskiRybalchenkoLICS2004Fig1.jar','PodelskiRybalchenkoLICS2004Fig1', "loop", None),

    # ##########################
    # Bugs, Unknown, and other
    # ##########################
    # TODO this should not work, but it says it does. It has nested loops, hence it should not work. I think this is a bug in the checker
    ('termination-suite/termination-crafted-lit/terminating/BrockschmidtCookFuhs-CAV2013-Fig1/BrockschmidtCookFuhsCAV2013Fig1.jar',
    'BrockschmidtCookFuhsCAV2013Fig1', "loop", anticorr_sumofrelu),

    # ##########################
    # Pathological Cases
    # ##########################
    (
    'termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.01/ChenFlurMukhopadhyaySAS2012Ex201.jar',
    'ChenFlurMukhopadhyaySAS2012Ex201', "loop", anticorr_sumofrelu),
    (
    'termination-suite/termination-crafted-lit/terminating/LeikeHeizmann-TACAS2014-Fig1/LeikeHeizmannTACAS2014Fig1.jar',
    'LeikeHeizmannTACAS2014Fig1', "loop", anticorr_sumofrelu),
    (
    'termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex1.01/ChenFlurMukhopadhyaySAS2012Ex101.jar',
    'ChenFlurMukhopadhyaySAS2012Ex101', "loop", None),  # PATHOLOGICAL CASE, short traces

]

    # ##########################
    # Not supported operations
    # ##########################

sv_comp_unsupported =[

    #Uses Java.util.Random()
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex3.09/ChenFlurMukhopadhyaySAS2012Ex309.jar','ChenFlurMukhopadhyaySAS2012Ex309', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-aaron2/AliasDarteFeautrierGonnordSAS2010aaron2.jar', 'AliasDarteFeautrierGonnordSAS2010aaron2', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/LeikeHeizmann-TACAS2014-Ex8/LeikeHeizmannTACAS2014Ex8.jar', 'LeikeHeizmannTACAS2014Ex8', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.22/ChenFlurMukhopadhyaySAS2012Ex222.jar','ChenFlurMukhopadhyaySAS2012Ex222', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-random1d-1/AliasDarteFeautrierGonnordSAS2010random1d1.jar', 'AliasDarteFeautrierGonnordSAS2010random1d1', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/CookSeeZuleger-TACAS2013-Fig7b/CookSeeZulegerTACAS2013Fig7b.jar','CookSeeZulegerTACAS2013Fig7b', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChenCookFuhsNimkarOHearn-TACAS2014-Introduction/ChenCookFuhsNimkarOHearnTACAS2014Introduction.jar','ChenCookFuhsNimkarOHearnTACAS2014Introduction', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-random2d/AliasDarteFeautrierGonnordSAS2010random2d.jar','AliasDarteFeautrierGonnordSAS2010random2d', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-aaron6/ChawdharyCookGulwaniSagivYangESOP2008aaron6.jar','ChawdharyCookGulwaniSagivYangESOP2008aaron6', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-random1d/ChawdharyCookGulwaniSagivYangESOP2008random1d.jar','ChawdharyCookGulwaniSagivYangESOP2008random1d', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/Masse-VMCAI2014-Fig1b/MasseVMCAI2014Fig1b.jar','MasseVMCAI2014Fig1b', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-exmini/AliasDarteFeautrierGonnordSAS2010exmini.jar','AliasDarteFeautrierGonnordSAS2010exmini', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-rsd/AliasDarteFeautrierGonnordSAS2010rsd.jar','AliasDarteFeautrierGonnordSAS2010rsd', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-aaron4/ChawdharyCookGulwaniSagivYangESOP2008aaron4.jar','ChawdharyCookGulwaniSagivYangESOP2008aaron4', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/UrbanMine-ESOP2014-Fig3/UrbanMineESOP2014Fig3.jar','UrbanMineESOP2014Fig3', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-aaron3/AliasDarteFeautrierGonnordSAS2010aaron3.jar','AliasDarteFeautrierGonnordSAS2010aaron3', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-aaron1/ChawdharyCookGulwaniSagivYangESOP2008aaron1.jar','ChawdharyCookGulwaniSagivYangESOP2008aaron1', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig6/HeizmannHoenickeLeikePodelskiATVA2013Fig6.jar','HeizmannHoenickeLeikePodelskiATVA2013Fig6', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-aaron12/ChawdharyCookGulwaniSagivYangESOP2008aaron12.jar','ChawdharyCookGulwaniSagivYangESOP2008aaron12', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/Ben-Amram-LMCS2010-Ex2.3/BenAmramLMCS2010Ex23.jar','BenAmramLMCS2010Ex23', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-aaron3/ChawdharyCookGulwaniSagivYangESOP2008aaron3.jar','ChawdharyCookGulwaniSagivYangESOP2008aaron3', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-random2d/ChawdharyCookGulwaniSagivYangESOP2008random2d.jar','ChawdharyCookGulwaniSagivYangESOP2008random2d', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-Fig1/AliasDarteFeautrierGonnordSAS2010Fig1.jar','AliasDarteFeautrierGonnordSAS2010Fig1', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/BradleyMannaSipma-ICALP2005-Fig1/BradleyMannaSipmaICALP2005Fig1.jar', 'BradleyMannaSipmaICALP2005Fig1', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/KroeningSharyginaTsitovichWintersteiger-CAV2010-Ex/KroeningSharyginaTsitovichWintersteigerCAV2010Ex.jar','KroeningSharyginaTsitovichWintersteigerCAV2010Ex', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-Fig2b/AliasDarteFeautrierGonnordSAS2010Fig2b.jar','AliasDarteFeautrierGonnordSAS2010Fig2b', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex1.03/ChenFlurMukhopadhyaySAS2012Ex103.jar','ChenFlurMukhopadhyaySAS2012Ex103', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-Fig2a/AliasDarteFeautrierGonnordSAS2010Fig2a.jar','AliasDarteFeautrierGonnordSAS2010Fig2a', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex1.05/ChenFlurMukhopadhyaySAS2012Ex105.jar','ChenFlurMukhopadhyaySAS2012Ex105', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex1.04/ChenFlurMukhopadhyaySAS2012Ex104.jar','ChenFlurMukhopadhyaySAS2012Ex104', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex2.20/ChenFlurMukhopadhyaySAS2012Ex220.jar','ChenFlurMukhopadhyaySAS2012Ex220', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-counterex1a/AliasDarteFeautrierGonnordSAS2010counterex1a.jar','AliasDarteFeautrierGonnordSAS2010counterex1a', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/CookSeeZuleger-TACAS2013-Fig1/CookSeeZulegerTACAS2013Fig1.jar','CookSeeZulegerTACAS2013Fig1', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/CookSeeZuleger-TACAS2013-Fig7a/CookSeeZulegerTACAS2013Fig7a.jar','CookSeeZulegerTACAS2013Fig7a', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChenFlurMukhopadhyay-SAS2012-Ex1.02/ChenFlurMukhopadhyaySAS2012Ex102.jar','ChenFlurMukhopadhyaySAS2012Ex102', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-random1d-2/AliasDarteFeautrierGonnordSAS2010random1d2.jar','AliasDarteFeautrierGonnordSAS2010random1d2', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/HeizmannHoenickeLeikePodelski-ATVA2013-Fig7/HeizmannHoenickeLeikePodelskiATVA2013Fig7.jar','HeizmannHoenickeLeikePodelskiATVA2013Fig7', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/ChawdharyCookGulwaniSagivYang-ESOP2008-aaron2/ChawdharyCookGulwaniSagivYangESOP2008aaron2.jar','ChawdharyCookGulwaniSagivYangESOP2008aaron2', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/AliasDarteFeautrierGonnord-SAS2010-counterex1b/AliasDarteFeautrierGonnordSAS2010counterex1b.jar','AliasDarteFeautrierGonnordSAS2010counterex1b', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/min_rf/MinRf.jar', 'MinRf', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/GulwaniJainKoskinen-PLDI2009-Fig1/GulwaniJainKoskinenPLDI2009Fig1.jar','GulwaniJainKoskinenPLDI2009Fig1', "loop", None),

    # Sequential while loops
    ('termination-suite/termination-crafted-lit/terminating/GulavaniGulwani-CAV2008-Fig1b/GulavaniGulwaniCAV2008Fig1b.jar', 'GulavaniGulwaniCAV2008Fig1b', "loop", None),
    ('termination-suite/termination-crafted-lit/terminating/Avery-FLOPS2006-Table1/AveryFLOPS2006Table1.jar','AveryFLOPS2006Table1', "loop", None),

]



nla_term = [

    # Works
    ('termination-suite/nla-term/prodbin-both-t/prodbinbotht.jar', 'prodbinbotht', "loop", None),

    # ######
    # Dynamite proves with single RF
    # ######
    # We learn + k  but not -c even though before rounding we have -c most of the time.
    ('termination-suite/nla-term/bresenham1-both-t/bresenham1botht.jar', 'bresenham1botht', "loop", None),
    # - c + k is a ranking function according to dynamite paper. Before rounding we have this as a subterm
    ('termination-suite/nla-term/cohencu5-both-t/cohencu5botht.jar', 'cohencu5botht', "loop", None),
    # we learn a - n which is supposed to be a rf but rounding destroys it
    ('termination-suite/nla-term/cohencu6-both-t/cohencu6botht.jar', 'cohencu6botht', "loop", None),
    # we learn a - n which is supposed to be a rf but rounding destroys it
    ('termination-suite/nla-term/cohencu7-both-t/cohencu7botht.jar', 'cohencu7botht', "loop", None),

    # Two Sequential While loops
    ('termination-suite/nla-term/dijkstra1-both-t/dijkstra1botht.jar', 'dijkstra1botht', "loop", None),
    ('termination-suite/nla-term/dijkstra2-both-t/dijkstra2botht.jar', 'dijkstra2botht', "loop", None),
    ('termination-suite/nla-term/dijkstra3-both-t/dijkstra3botht.jar', 'dijkstra3botht', "loop", None),
    ('termination-suite/nla-term/hard2-both-t/hard2botht.jar', 'hard2botht', "loop", None),

    # We learn and round 1 * y3 but for some reason the verification fails even thought the dynamite paper says that's
    # the RF
    ('termination-suite/nla-term/mannadiv-both-t/mannadivbotht.jar', 'mannadivbotht', "loop", anticorr_sumofrelu),

    # We learn k - c  before rounding but after rounding the c is gone
    ('termination-suite/nla-term/ps2-both-t/ps2botht.jar', 'ps2botht', "loop", None),
    ('termination-suite/nla-term/ps3-both-t/ps3botht.jar', 'ps3botht', "loop", None),
    ('termination-suite/nla-term/ps4-both-t/ps4botht.jar', 'ps4botht', "loop", None),

    # get's somewhat learned before rounding
    ('termination-suite/nla-term/sqrt1-both-t/sqrt1botht.jar', 'sqrt1botht', "loop", None),

    # Nested loops
    ('termination-suite/nla-term/fermat1-both-t/fermat1botht.jar', 'fermat1botht', "loop", None),

    # Comes close but rounding does weird things. In Dynamite paper the RF is: -r + 12a +3k
    ('termination-suite/nla-term/freire1-both-t/freire1botht.jar', 'freire1botht', "loop", None),




    # ######
    # Dynamite proves with COMPOSITIONAL RF
    # ######
    ('termination-suite/nla-term/cohencu1-both-t/cohencu1botht.jar', 'cohencu1botht', "loop", None),
    ('termination-suite/nla-term/cohencu2-both-t/cohencu2botht.jar', 'cohencu2botht', "loop", None),
    ('termination-suite/nla-term/cohencu3-both-t/cohencu3botht.jar', 'cohencu3botht', "loop", None),
    ('termination-suite/nla-term/cohencu4-both-t/cohencu4botht.jar', 'cohencu4botht', "loop", None),


    # One get's learned k - c
    ('termination-suite/nla-term/ps6-both-t/ps6botht.jar', 'ps6botht', "loop", None),

    # -x or k - c... get's somewhat learned before rouding
    ('termination-suite/nla-term/ps5-both-t/ps5botht.jar', 'ps5botht', "loop", None),

    # Two sequential while loops
    ('termination-suite/nla-term/dijkstra4-both-t/dijkstra4botht.jar', 'dijkstra4botht', "loop", None),
    ('termination-suite/nla-term/dijkstra5-both-t/dijkstra5botht.jar', 'dijkstra5botht', "loop", None),
    ('termination-suite/nla-term/dijkstra6-both-t/dijkstra6botht.jar', 'dijkstra6botht', "loop", None),
    ('termination-suite/nla-term/hard-both-t/hardbotht.jar', 'hardbotht', "loop", None),

    #
    ('termination-suite/nla-term/geo3-both-t/geo3botht.jar', 'geo3botht', "loop", None),
    ('termination-suite/nla-term/geo1-both-t/geo1botht.jar', 'geo1botht', "loop", None),
    ('termination-suite/nla-term/geo2-both-t/geo2botht.jar', 'geo2botht', "loop", None),
    ('termination-suite/nla-term/egcd3-both-t/egcd3botht.jar', 'egcd3botht', "loop", None),
    ('termination-suite/nla-term/prod4br-both-t/prod4brbotht.jar', 'prod4brbotht', "loop", None),
    ('termination-suite/nla-term/egcd-both-t/egcdbotht.jar', 'egcdbotht', "loop", None),


    #unknown
    ('termination-suite/nla-term/egcd2-both-t/egcd2botht.jar', 'egcd2botht', "loop", None),

]

datatype_bm = [
    ('examples/PaperEx1/PaperEx1.jar', 'classes.PaperEx1', 'removeNegative', None),
]

lst ="AliasDarteFeautrierGonnordSAS201CookSeeZulegerTACAS2013Fig8a0speedpldi4 ChawdharyCookGulwaniSagivYangESOP2008easy1 AliasDarteFeautrierGonnordSAS2010easy1 BradleyMannaSipmaCAV2005Fig1 LeikeHeizmannTACAS2014Ex7 AliasDarteFeautrierGonnordSAS2010easy21 ChenFlurMukhopadhyaySAS2012Ex210 ChenFlurMukhopadhyaySAS2012Ex308 Aviad AliasDarteFeautrierGonnordSAS2010ndecr GulavaniGulwaniCAV2008Fig1c HeizmannHoenickeLeikePodelskiATVA2013Fig8 CookSeeZulegerTACAS2013Fig8amodified Genady HeizmannHoenickeLeikePodelskiATVA2013Fig9 ChenFlurMukhopadhyaySAS2012Ex219 ChenFlurMukhopadhyaySAS2012Ex207 LeikeHeizmannWST2014Ex9 ChawdharyCookGulwaniSagivYangESOP2008easy2 LeikeHeizmannTACAS2014Ex1 HeizmannHoenickeLeikePodelskiATVA2013Fig4 LeikeHeizmannTACAS2014Ex9 AliasDarteFeautrierGonnordSAS2010wise AliasDarteFeautrierGonnordSAS2010easy22 ChenFlurMukhopadhyaySAS2012Ex213 HeizmannHoenickeLeikePodelskiATVA2013Fig5modified ChenFlurMukhopadhyaySAS2012Ex301 HeizmannHoenickeLeikePodelskiATVA2013Fig1 PodelskiRybalchenkoTACAS2011Fig1 PodelskiRybalchenkoTACAS2011Fig2 AliasDarteFeautrierGonnordSAS2010speedFails4 HeizmannHoenickeLeikePodelskiATVA2013Fig5 NoriSharmaFSE2013Fig7 ChenFlurMukhopadhyaySAS2012Ex310 GopanRepsCAV2006Fig1a ChenFlurMukhopadhyaySAS2012Ex304 MasseVMCAI2014Ex6 ChenFlurMukhopadhyaySAS2012Ex206 AliasDarteFeautrierGonnordSAS2010speedpldi2 ChenFlurMukhopadhyaySAS2012Ex307 AliasDarteFeautrierGonnordSAS2010speedpldi3 ChenFlurMukhopadhyaySAS2012Ex208 ChenFlurMukhopadhyaySAS2012Ex221 BrockschmidtCookFuhsCAV2013Introduction AliasDarteFeautrierGonnordSAS2010terminate PodelskiRybalchenkoVMCAI2004Ex2 HeizmannHoenickeLeikePodelskiATVA2013Fig2 GulavaniGulwaniCAV2008Fig1a ChenFlurMukhopadhyaySAS2012Ex305 ChenFlurMukhopadhyaySAS2012Ex401 KroeningSharyginaTsitovichWintersteigerCAV2010Fig1 CookSeeZulegerTACAS2013Fig8b MasseVMCAI2014Fig1a ChenFlurMukhopadhyaySAS2012Ex216 AliasDarteFeautrierGonnordSAS2010cousot9 ChenFlurMukhopadhyaySAS2012Ex303 ColonSipmaTACAS2001Fig1 ChenFlurMukhopadhyaySAS2012Fig1 NoriSharmaFSE2013Fig8 ChenFlurMukhopadhyaySAS2012Ex218 ChenFlurMukhopadhyaySAS2012Ex209 LarrazOliverasRodriguezCarbonellRubioFMCAD2013Fig1 UrbanWST2013Fig2 AliasDarteFeautrierGonnordSAS2010wcet2 BrockschmidtCookFuhsCAV2013Fig9a AliasDarteFeautrierGonnordSAS2010complex AliasDarteFeautrierGonnordSAS2010while2 AliasDarteFeautrierGonnordSAS2010loops PodelskiRybalchenkoLICS2004Fig1 BrockschmidtCookFuhsCAV2013Fig1 ChenFlurMukhopadhyaySAS2012Ex201 LeikeHeizmannTACAS2014Fig1 ChenFlurMukhopadhyaySAS2012Ex101"


if __name__ == '__main__':
    print(len(sv_comp_termination))
    print(len(lst.split(" ")))

    sv_ = list(map(lambda x: x[1], sv_comp_termination))
    ss_ = lst.split(" ")

    print([x for x in sv_ if x not in ss_])
    exit(0)

