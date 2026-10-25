module

public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackCandidateFamily
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackAccessibilityDetection
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFullModel

/-!
概要：引き戻しの小さい候補族の張る全部分圏を、小さい ∞ 圏で模型化する。
方針：両成分の固定頂点写像の小ささを引き戻しへ移し、既存の全部分模型を使う。
規約：compact 性と生成性は別の工程とし、模型自体の充填性・充満忠実性を構成する。
使われ方：引き戻しの accessibility の生成圏候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {E D B : SSet.{u + 1}} [Quasicategory B]
  (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p) (hB : IsLocallySmall B)
  (hE : Ind.HasSmallFixedVertexMaps E) (hD : Ind.HasSmallFixedVertexMaps D)
  {AE AD : Type u} (vE : AE → E _⦋0⦌) (vD : AD → D _⦋0⦌)

/-- 概要：引き戻しの全候補の張る小さい全部分模型。
方針：元の候補の値上の全部分複体を全次数で縮小する。
規約：小さい宇宙 u の模型。
使われ方：compact 生成圏の構成で用いる候補。 -/
def pullbackCandidateCategory : SSet.{u} :=
  smallFullModel (pullback_hasSmallFixedVertexMaps p q hE hD)
    (pullbackCandidateFamily p q hB vE vD hp)

/-- 概要：小さい候補模型は ∞ 圏。
方針：一方の同値持ち上げから引き戻しの充填性を得て、縮小へ反映する。
規約：元の両始域を ∞ 圏とする。
使われ方：生成圏候補の束縛。 -/
instance pullbackCandidateCategory_quasicategory [Quasicategory E] [Quasicategory D] :
    Quasicategory (pullbackCandidateCategory p q hp hB hE hD vE vD) := by
  have : InnerFibration p := hp.innerFibration
  have : Quasicategory (pullback p q) := inferInstance
  exact smallFullModel_quasicategory _ _

/-- 概要：小さい候補模型から元の引き戻しへの全包含。
方針：縮小の同型と元の全部分包含を合成する。
規約：元の候補族を張る全部分圏の包含。
使われ方：生成表示を元の引き戻し内へ送る関手。 -/
def pullbackCandidateInclusion :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (pullbackCandidateCategory p q hp hB hE hD vE vD) ⟶ pullback p q :=
  smallFullModelInclusion (pullback_hasSmallFixedVertexMaps p q hE hD)
    (pullbackCandidateFamily p q hB vE vD hp)

/-- 概要：候補模型の包含は全写像空間で充満忠実。
方針：縮小同型と元の全部分包含の充満忠実性を使う。
規約：生成性を入力に要求しない。
使われ方：小さい compact 生成圏の候補の充満性。 -/
lemma pullbackCandidateInclusion_isFullyFaithful [Quasicategory E] [Quasicategory D] :
    IsFullyFaithful (pullbackCandidateInclusion p q hp hB hE hD vE vD) := by
  have : InnerFibration p := hp.innerFibration
  have : Quasicategory (pullback p q) := inferInstance
  exact smallFullModelInclusion_isFullyFaithful _ _

end SerrePositivity.InfinityCategories.F2.Presentable
