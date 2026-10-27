module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionProjectionNaturality
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientVerdierSequence

/-!
概要：固定 strict data の商射を、元の cone 射の ∞ 側の降下として同定する。
方針：既存の固定 augmentation 屋根比較を用い、商の全関手圏の充満忠実性で同型を反映する。
規約：ε 整合 Hom や cell 比較関手の native Hom 作用は要求しない。
使われ方：StableInfinity 側で選んだ降下関手との照合。独自集約・監査のみ登録する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.NonConnective SSet MonoidalClosed
open scoped Simplicial
variable (R : Type u) [CommRing R] (A B : Type v)
  [DGCategory R A] [Small.{u} A] [DGCategory R B] [Small.{u} B]
  {κ : Cardinal.{u}} (IA : DGKappaConeInput R A κ) (IB : DGKappaConeInput R B κ)
  (d : DGKappaSuspensionMapData R A B IA IB)

/-- 固定 Q(data) と元の cone 関手を結ぶ、指定された ∞ 側の三角形。
既存の正本比較を保持し、augmentation の逆や商射を選び直さない。 -/
def dgSuspensionQuotientTriangle :
    FunctorIso (dgKappaSuspensionProjection R A IA ≫
      dgNerve.map (dgKappaSuspensionInputMap R A B IA IB d).down)
      (dgNerve.map d.cone ≫ dgKappaSuspensionProjection R B IB) :=
  dgKappaSuspensionProjectionNaturality R A B IA IB d

/-- 商の全完全関手圏の普遍性の基礎となる、全関手圏の充満忠実性。 -/
theorem dgSuspensionQuotientPrecomposition_isFullyFaithful
    (Y : SSet.{max (u + 1) v}) [Quasicategory Y] :
    IsFullyFaithful ((pre (dgKappaSuspensionProjection R A IA)).app Y) :=
  resolvedDGQuotientPrecomposition_isFullyFaithful R (DGKappaCone R A IA)
    (dgKappaConePerfectObjects R A IA) Y

/-- 同じ cone 射の降下三角形を持つ任意の関手は、固定 Q(data) と全関手同型になる。
G の存在を仮定から作らない。供給された G と三角形を、固定商射へ照合する入口。 -/
def dgSuspensionQuotientDescentComparison
    (G : dgKappaSuspensionInfinity R A IA ⟶ dgKappaSuspensionInfinity R B IB)
    (hG : FunctorIso (dgKappaSuspensionProjection R A IA ≫ G)
      (dgNerve.map d.cone ≫ dgKappaSuspensionProjection R B IB)) :
    FunctorIso (dgNerve.map (dgKappaSuspensionInputMap R A B IA IB d).down) G := by
  apply (dgSuspensionQuotientPrecomposition_isFullyFaithful R A IA
    (dgKappaSuspensionInfinity R B IB)).preimageVertexIso
  exact dgSuspensionQuotientTriangle R A B IA IB d ≪≫ hG.symm

/-- cone 間の ∞ 関手同型は、二つの固定 strict data の商射間へ降下する。
商間の厳密 dg 関手圏の native 同型へは強めない。 -/
def dgSuspensionQuotientConeComparison
    (e : DGKappaSuspensionMapData R A B IA IB)
    (h : FunctorIso (dgNerve.map d.cone) (dgNerve.map e.cone)) :
    FunctorIso (dgNerve.map (dgKappaSuspensionInputMap R A B IA IB d).down)
      (dgNerve.map (dgKappaSuspensionInputMap R A B IA IB e).down) := by
  apply (dgSuspensionQuotientPrecomposition_isFullyFaithful R A IA
    (dgKappaSuspensionInfinity R B IB)).preimageVertexIso
  exact dgSuspensionQuotientTriangle R A B IA IB d ≪≫
    h.postcomp (dgKappaSuspensionProjection R B IB) ≪≫
      (dgSuspensionQuotientTriangle R A B IA IB e).symm

/-- perfect 保存だけから、cone 射は実 Verdier 商上に完全な ∞ 関手として降下する。 -/
theorem dgSuspensionQuotientDescent_exists :
    ∃ G : dgKappaSuspensionInfinity R A IA ⟶ dgKappaSuspensionInfinity R B IB,
      IsExactFunctor G ∧ Nonempty (FunctorIso (dgKappaSuspensionProjection R A IA ≫ G)
        (dgNerve.map d.cone ≫ dgKappaSuspensionProjection R B IB)) := by
  let := dgKappaSuspensionInfinity_isStable R B IB
  let : IsExactFunctor (dgNerve.map d.cone) :=
    dgPretriangulatedFunctor_isExactFunctor R _ _ d.cone
  let : IsExactFunctor (dgKappaSuspensionProjection R B IB) :=
    resolvedDGQuotientFunctor_isExactFunctor R (DGKappaCone R B IB)
      (dgKappaConePerfectObjects R B IB)
  let F := dgNerve.map d.cone ≫ dgKappaSuspensionProjection R B IB
  let : IsExactFunctor F := isExactFunctor_comp _ _
  apply resolvedDGVerdierExactFunctor_extension_exists R (DGKappaCone R A IA)
    (dgKappaConePerfectObjects R A IA) F
  intro b
  change IsZeroVertex ((dgKappaSuspensionProjection R B IB).app _
    ((dgNerve.map d.cone).app _ (DGNerve.Simplex.vertex b.val)))
  rw [dgFunctorNerve_vertex]
  exact resolvedDGQuotientFunctor_kills R (DGKappaCone R B IB)
    (dgKappaConePerfectObjects R B IB) ⟨d.cone.obj b.val, d.preservesPerfect _ b.property⟩

/-- 全完全関手圏の普遍性で選んだ cone 射の実降下。固定 Q(data) からは定義しない。 -/
def dgSuspensionQuotientUniversalDescent :
    dgKappaSuspensionInfinity R A IA ⟶ dgKappaSuspensionInfinity R B IB :=
  Classical.choose (dgSuspensionQuotientDescent_exists R A B IA IB d)

/-- 普遍性で選んだ同じ降下は完全である。 -/
theorem dgSuspensionQuotientUniversalDescent_isExact :
    IsExactFunctor (dgSuspensionQuotientUniversalDescent R A B IA IB d) :=
  (Classical.choose_spec (dgSuspensionQuotientDescent_exists R A B IA IB d)).1

/-- 普遍性で選んだ同じ降下の、元の cone 射への三角形。 -/
def dgSuspensionQuotientUniversalDescent_triangle :
    FunctorIso (dgKappaSuspensionProjection R A IA ≫
      dgSuspensionQuotientUniversalDescent R A B IA IB d)
      (dgNerve.map d.cone ≫ dgKappaSuspensionProjection R B IB) :=
  Classical.choice
    (Classical.choose_spec (dgSuspensionQuotientDescent_exists R A B IA IB d)).2

/-- 固定 Q(data) を、全完全関手圏の普遍性から選んだ同じ降下と同定する実比較。 -/
def dgSuspensionQuotientUniversalDescentComparison :
    FunctorIso (dgNerve.map (dgKappaSuspensionInputMap R A B IA IB d).down)
      (dgSuspensionQuotientUniversalDescent R A B IA IB d) :=
  dgSuspensionQuotientDescentComparison R A B IA IB d _
    (dgSuspensionQuotientUniversalDescent_triangle R A B IA IB d)

end SerrePositivity.InfinityCategories
