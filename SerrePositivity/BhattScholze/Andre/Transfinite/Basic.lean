module

public import SerrePositivity.BhattScholze.Andre.Transfinite.RootClosure
public import SerrePositivity.BhattScholze.Andre.Transfinite.ResidueFrobenius
public import SerrePositivity.BhattScholze.Andre.Transfinite.CountableDescent
public import SerrePositivity.BhattScholze.Andre.Transfinite.CountableCompletion
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidLimitCompleteness
public import SerrePositivity.BhattScholze.Andre.Transfinite.OmegaOne
public import SerrePositivity.BhattScholze.Andre.Transfinite.CompleteFlatColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.FaithfullyFlatColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.ResidueTensorColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.Composition
public import SerrePositivity.BhattScholze.Andre.Transfinite.TorsionBound
public import SerrePositivity.BhattScholze.Andre.Transfinite.FrobeniusKernelColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.PrismaticCompletion
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectDeltaColimit

public import SerrePositivity.BhattScholze.Andre.Transfinite.PresentationColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidCompletionColimit

public import SerrePositivity.BhattScholze.Andre.Transfinite.BoundedCompletion

public import SerrePositivity.BhattScholze.Andre.Transfinite.Terminal

public import SerrePositivity.BhattScholze.Andre.Transfinite.CountableRelations

public import SerrePositivity.BhattScholze.Andre.Transfinite.AlgebraColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.CompletionUniversal

public import SerrePositivity.BhattScholze.Andre.Transfinite.AlgebraCategory

public import SerrePositivity.BhattScholze.Andre.Transfinite.Existence

public import SerrePositivity.BhattScholze.Andre.Transfinite.SingleRoot

/-! # André E3：超限反復の部品

BS Thm 7.14（著者版 p.61）。現時点では剰余 Frobenius の保存、
可算データの降下、非可算共終性と単射性の下での完備性、根を持つ有向系の絶対整閉性を集約する。
最小元を持つ有向系の p 進完備化の perfectoid 性も証明する。
有界ねじれによる完備化の完全忠実平坦性と ω₁ 塔の終段の三性質を証明する。
訂正済み一段拡大 step を明示仮定として、ω₁ までの超限塔と Thm 7.14 の存在結論を証明する。
step の A1 による解消と Inputs の置換はまだ行っていない。
-/
