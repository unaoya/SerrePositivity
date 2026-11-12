module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismCutDiagonalMaximum
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutRightEndpoint

/-!
概要：二つの順序づけられた時刻切断で、第一射の最大座標を元の最後の零頂点へ戻す。
方針：内側の零頂点を外側切断が保持することから、最大元の両方向の不等式を示す。
規約：切断後の path の終点は最後の頂点に限らない。
使われ方：第二三角形の二つの可変 Hom を同時に照合する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 内側の零頂点を保つ外側切断の像で、第一射の最大座標は元の最後の零頂点。 -/
lemma pathCutMaximum_eq_lastZero_of_nestedCut {n : ℕ}
    (s t : Fin (n + 1) →o Fin 2) (hst : ∀ k, t k = 0 → s k = 0)
    {i j : Fin (n + 1)} (hi : t i = 0)
    (R : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    {j' : Fin (n + 2)}
    (Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j'))
    (hQ : Q.I = (fun k : ULift.{u} (Fin (n + 1)) ↦
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s k.down)) '' R.I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi R := by
  apply le_antisymm
  · have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi Q
    have hmem := hm.2
    rw [hQ] at hmem
    obtain ⟨⟨k⟩, hk, he⟩ := hmem
    by_cases hs : s k = 0
    · have he' : k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q := Fin.castSucc_inj.mp
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s k hs).symm.trans (ULift.ext_iff.mp he))
      rw [← he']
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero t hi R k (he' ▸ hm.1) hk
    · have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) ↦ a.down.val) he
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s k).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q).val at he'
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one s k hs] at he'
      have hlt := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q).isLt
      change n + 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q).val at he'
      omega
  · have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi R
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutMaximum t hi Q _ hm.1
    rw [hQ]
    exact ⟨ULift.up _, hm.2,
      congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s _ (hst _ hm.1))⟩

/-- 同じ二重切断の像の最大座標射は、元の最後の零頂点の射そのもの。 -/
lemma coherentNestedCut_maximumMap {n : ℕ}
    (s t : Fin (n + 1) →o Fin 2) (hst : ∀ k, t k = 0 → s k = 0)
    (i j : Fin (n + 1)) (hi : t i = 0) {j' : Fin (n + 2)}
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s j = j') :
    ((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
          (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s i (hst i hi)) hj)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap t hi j := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro R
  apply stdSimplex.ext
  intro k
  apply pathCutMaximum_eq_lastZero_of_nestedCut s t hst hi (R.obj k)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningHom_transport_I
    (congrArg (fun a : Fin (n + 2) ↦
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s i (hst i hi)))
    (congrArg (fun a : Fin (n + 2) ↦
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))) hj)
    (((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩).app (Opposite.op ⦋d⦌) R) k

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
