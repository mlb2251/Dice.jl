include("benchmarks.jl")

GENERATION_PARAMS_LIST = [
    # LangBespokeSTLCGenerator(
    #     expr_size=5,
    #     typ_size=2,
    # ),
    # LangSiblingDerivedGenerator{STLC}(
    #     root_ty=Expr.t,
    #     ty_sizes=[Expr.t=>5, Typ.t=>2],
    #     stack_size=2,
    #     intwidth=3,
    # )
    LangSiblingDerivedGenerator{RBT}(
        root_ty=ColorKVTree.t,
        ty_sizes=[ColorKVTree.t=>4, Color.t=>0],
        stack_size=2,
        intwidth=3,
    )
#    LangSiblingDerivedGenerator{BST}(
#        root_ty=KVTree.t,
#        ty_sizes=[KVTree.t=>4],
#        stack_size=2,
#        intwidth=3,
#    ),
]
# LR_LIST = [0.3]
LR_LIST = [0.003, 0.01, 0.03, 0.1, 0.3]
FP_LIST = [0.]
FORIGIVENESS_LIST = [0]
RAND_FORIGIVENESS_LIST = [true]
RESAMPLING_FREQUENCY_LIST = [2]
# PROPERTY_LIST = [BSTOrderInvariant()]
# PROPERTY_LIST = [MultipleInvariants([
#     BookkeepingInvariant(),
#     BalanceInvariant(),
#     OrderInvariant(),
# ]),
# TrueProperty{RBT}()]

PROPERTY_LIST = [nothing]

SAMPLES_PER_BATCH_LIST = [200]
EPOCHS_LIST = [2000]

# SAMPLES_PER_BATCH_LIST = [nothing]
BOUND_LIST = [0, 0.1]

EQ_LIST = [:prob_equals]

n_runs = prod(map(length, [GENERATION_PARAMS_LIST, LR_LIST, FP_LIST, FORIGIVENESS_LIST, RAND_FORIGIVENESS_LIST, PROPERTY_LIST, RESAMPLING_FREQUENCY_LIST, SAMPLES_PER_BATCH_LIST, EPOCHS_LIST, EQ_LIST, BOUND_LIST]))
println(n_runs)
@assert n_runs <= 12

@show GENERATION_PARAMS_LIST
@show LR_LIST
@show FP_LIST
@show FORIGIVENESS_LIST
@show RAND_FORIGIVENESS_LIST
@show PROPERTY_LIST
@show RESAMPLING_FREQUENCY_LIST
@show SAMPLES_PER_BATCH_LIST
@show EPOCHS_LIST
@show EQ_LIST
@show BOUND_LIST
println()

LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
    (
        [
            # ApproxSTLCConstructorEntropy() => lr,
            MLELossConfig{RBT}(RBTDepth(), Uniform()) => lr,
#             SamplingEntropy{RBT}(
#                 resampling_frequency=resampling_frequency,
#                 samples_per_batch=samples_per_batch,
#                 property=property,
#                 eq=eq,
#                 failure_penalty=fp,
#                 forgiveness=forgiveness,
#                 rand_forgiveness=rand_forgiveness,
#                 keyf=:identity,
#             ) => lr,
# #             # SamplingEntropy{BST}(
            #     resampling_frequency=resampling_frequency,
            #     samples_per_batch=samples_per_batch,
            #     property=BSTOrderInvariant(),
            #     eq=eq,
            #     failure_penalty=fp,
            # ) => lr,
            # SamplingEntropy{RBT}(
            #     resampling_frequency=resampling_frequency,
            #     samples_per_batch=samples_per_batch,
            #     property=MultipleInvariants([
            #         BookkeepingInvariant(),
            #         BalanceInvariant(),
            #         OrderInvariant(),
            #     ]),
            #     eq=eq,
            #     failure_penalty=fp,
            #     forgiveness=forgiveness,
            #     rand_forgiveness=rand_forgiveness,
            # ) => lr,
        ]
        for lr in LR_LIST
        for fp in FP_LIST
        for forgiveness in FORIGIVENESS_LIST
        for rand_forgiveness in RAND_FORIGIVENESS_LIST
        for property in PROPERTY_LIST
        for resampling_frequency in RESAMPLING_FREQUENCY_LIST
        for samples_per_batch in SAMPLES_PER_BATCH_LIST
        for eq in EQ_LIST
    ),
]))


# N = 4
# GENERATION_PARAMS_LIST = [Flips{N}()]
# # LR_LIST = [0.0001, 0.0003, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10, 30, 100, 300]
# LR_LIST = [0.0001, 0.0002, 0.0005, 0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1, 3, 10, 30, 100]
# LOSS_CONFIG_WEIGHT_PAIRS_LIST = collect(Iterators.flatten([
#     (
#         [
#             # BoolsExactEntropy{3}() => lr,
#             SamplingEntropy{Bools{N}}(resampling_frequency=10, samples_per_batch=100) => lr,
#         ]
#         for lr in LR_LIST
#     ),
# ]))
# EPOCHS_LIST = [10_000]

TOOL_PATH = "examples/qc/benchmarks/tool.jl"

@sync for (p, lcws, epochs, bound) in Base.product(GENERATION_PARAMS_LIST, LOSS_CONFIG_WEIGHT_PAIRS_LIST, EPOCHS_LIST, BOUND_LIST)
    flags = join([s for s in ARGS if startswith(s, "-")], " ")
    lcws_s = replace(string(lcws), " "=>"")
    p_s = replace(string(p), " "=>"")
    s = "julia --project $(TOOL_PATH) $(flags) $(p_s) $(lcws_s) $(epochs) $(bound)"
    cmd = Cmd(Cmd(convert(Vector{String}, split(s))), ignorestatus=true)
    println(s)
    out = IOBuffer()
    @async begin
        proc = run(pipeline(cmd; stdout=out, stderr=stdout),)
        if proc.exitcode != 0
            println()
            println(proc.exitcode)
            so = String(take!(out))
            println("FAILED: $(s)\nSTDOUT ===\n$(so)\n\n")
        end
    end
end

