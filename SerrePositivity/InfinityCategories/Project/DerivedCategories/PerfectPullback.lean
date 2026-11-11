module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectInclusion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PullbackCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport

/-! # Perf の引き戻し判定

概要：D4 の標準 fiber による引き戻し判定を Perf に制限する。
方針：標準 fiber の完全性から極限錐を部分圏内へ持ち上げ、極限の一意性を使う。
規約：四角形は任意。使われ方：K 理論の G2 の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

private lemma lift_cone {K : SSet.{u + 1}} {p : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModel S}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S))
    (hc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S (c.vertex.obj 0)) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionCone S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S) d = c := by
  have hv : ∀ z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) K) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S ((c.val.app _ z).obj 0) := by
    rintro ⟨cut, x, y⟩
    fin_cases cut
    · change PUnit at x
      have hx : x = PUnit.unit := Subsingleton.elim _ _
      subst x
      have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) y) c.property
      change c.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K).app _ y) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S).app _ (p.app _ y) at h
      change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S ((c.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K).app _ y)).obj 0)
      rw [h]
      exact ((p.app _ y).obj 0).property
    · change PUnit at y
      change (Δ[0] : SSet.{u + 1}) _⦋0⦌ at x
      have hy : y = PUnit.unit := Subsingleton.elim _ _
      subst y
      have hx : x = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})) :=
        SSet.stdSimplex.obj₀Equiv.injective (by apply Fin.ext; omega)
      subst x
      exact hc
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S) c.val hv
  have hL : L ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S = c.val := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp _ _ _ _ _
  have hfixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ L = p := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S)).1
    rw [Category.assoc, hL]
    exact c.property
  exact ⟨⟨L, hfixed⟩, Subtype.ext hL⟩

private lemma preserve_limit_of_reference {K : SSet.{u + 1}} {p : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModel S}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) (hp : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S (d.vertex.obj 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionCone S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S) c) := by
  obtain ⟨d', he⟩ := lift_cone d hp
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isLimitCone_of_fullInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S) d' (he ▸ hd)
  let G := (SSet.hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S))).toFunctor
  have e := G.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso c d' hc hd')
  have hd'' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionCone S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S) d') :=
    he ▸ hd
  exact hd''.of_vertexIso e.symm

/-- 概要：完全対象の四角形から抽出する標準 fiber も完全である。
方針：cospan の三対象の完全性と直和・fiber の閉性を使う。
規約：極限性を仮定しない。使われ方：部分圏内の標準極限錐。 -/
lemma perfectSquareStandardFiber
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModel S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareStandardFiber (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S)) := by
  have hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel S
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S)).leftObj := by
    let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSemifree S) 1 := SSet.yonedaEquiv
      (SSet.horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)
    exact (s.obj 0).property
  have hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel S
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S)).rightObj := by
    let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSemifree S) 1 := SSet.yonedaEquiv
      (SSet.horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)
    exact (s.obj 0).property
  have hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel S
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S)).targetObj := by
    let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSemifree S) 1 := SSet.yonedaEquiv
      (SSet.horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)
    exact (s.obj 1).property
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_fiber S _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_binaryBiproduct S hB hC) hD

/-- 概要：Perf の計算モデル内の引き戻しは D(S) でも引き戻しである。
方針：完全な標準 fiber の極限錐を持ち上げ、元の極限錐と比較する。
規約：四角形の追加整合性は不要。使われ方：D4 の必要条件の制限。 -/
lemma perfectNerve_isPullbackSquare_map
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModel S)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S) := by
  let G := F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_cospan G).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare G))
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone_isLimit _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_isPullback G)
  have hp : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S (d.vertex.obj 0) := by
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare G)).vertex.obj 0)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_vertex]
    exact perfectSquareStandardFiber F
  exact preserve_limit_of_reference (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F) hF d hd hp

/-- 概要：Perf の計算モデルの四角形は D4 の比較射が擬同型であるとき、かつそのときに限り引き戻し。
方針：包含の引き戻し保存・反映と D4 の判定を合成する。
規約：任意の四角形。使われ方：Perf 上の導来引き戻し判定。 -/
theorem perfectNerve_isPullbackSquare_iff_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModel S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveInclusion S)) := by
  constructor
  · intro hF
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison_quasiIso _ (perfectNerve_isPullbackSquare_map F hF)
  · intro hF
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isPullbackSquare_of_fullInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S) F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derived_isPullbackSquare_of_quasiIso _ hF)

/-- 概要：正本の Perf の四角形にも D4 の擬同型判定が双方向に制限される。
方針：モデルとの単体的同型で極限性を移し、包含の一致式で比較射を同定する。
規約：元の充満部分単体集合内の任意の四角形。使われ方：K 理論側の引き戻し判定。 -/
theorem perfect_isPullbackSquare_iff_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔
      QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityInclusion S)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.isLimitCone_iff_mapJoinCone_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).inv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).inv) at h
  have h' := h.trans (perfectNerve_isPullbackSquare_iff_quasiIso
    (F ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).inv))
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso_inv_inclusion] at h'
  exact h'

end SerrePositivity.InfinityCategories.Project.DerivedCategories
