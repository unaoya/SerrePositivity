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

public import SerrePositivity.BhattScholze.Andre.Transfinite.Theorem714

public import SerrePositivity.BhattScholze.Andre.Transfinite.DirectedCompletion

/-!
# André E3：BS Thm 7.14 の超限反復と証明済み存在定理

## 概要

BS Thm 7.14（著者版 p.61）の第一文を、追加の存在仮定なしで証明する。
一般の非空有向系の完備化の perfectoid 性と完全忠実平坦性も供給する。

## 方針

A1 の完全 prism 商上の一元拡大を任意の perfectoid 基底へ移す。
固定した族の一元飽和で指定 step を証明し、全正次数モニックの根添加を ω₁ まで反復する。
終段は自動的に p 進完備な未完備余極限を使い、有限係数の降下から絶対整閉性を得る。

## 規約

環と反復の添字は Type u に留める。元の初段の標準係数作用に関して完全忠実平坦性を証明する。
有向余極限の保存には、添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方

`SerrePositivity.BhattScholze.Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`
が元の署名の無条件存在定理を供給する。
Inputs はこの無条件版の公開報告後、別保存単位で証明済み入口に置換した。
-/
