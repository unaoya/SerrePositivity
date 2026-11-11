module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismCutCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionEndpoints

/-!
概要：同じ時刻切断の像にある path の二つの合成座標は一致する。
方針：最後の頂点以外の像は全て零ラベルなので、最大元を取る集合が等しい。
規約：元の path の旗と端点の等号による移送を保持する。
使われ方：coherent 合成四角形の対角を元の豊穣合成の標準比較と同定する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 切断の像の path では、零ラベルの最大頂点と最後以前の最大頂点が一致する。 -/
lemma pathCutMaximum_eq_pathLastMaximum_of_cutImage {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) {i j : Fin (n + 1)} (hi : t i = 0)
    (R : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))
    (hQ : Q.I = (fun k : ULift.{u} (Fin (n + 1)) ↦
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t k.down)) '' R.I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi Q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum Q := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutBeforeLast t Q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast Q := by
    classical
    ext k
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutBeforeLast, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast, Finset.mem_filter, Finset.mem_univ,
      true_and, and_iff_right_iff_imp]
    intro hk
    rw [hQ] at hk
    obtain ⟨⟨l⟩, hl, he⟩ := hk
    by_cases ht : t l = 0
    · have he' : l = k := Fin.castSucc_inj.mp
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero t l ht).symm.trans (ULift.ext_iff.mp he))
      simpa only [he'] using ht
    · have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) ↦ a.down.val) he
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t l).val = k.val at he'
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t l ht] at he'
      have hk' := k.isLt
      change n + 1 = k.val at he'
      omega
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum
  simp only [h]

/-- 同じ切断後の旗では、合成の二つの最大座標射が一致する。 -/
lemma coherentPrismCut_diagonalMaximumMap {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j ≠ 0) :
    let D := (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
          (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero t i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t j hj))
    D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi (Fin.last (n + 1)) = D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i := by
  dsimp only
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro R
  apply stdSimplex.ext
  intro k
  apply pathCutMaximum_eq_pathLastMaximum_of_cutImage t hi (R.obj k)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningHom_transport_I
    (congrArg (fun a : Fin (n + 2) ↦
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero t i hi))
    (congrArg (fun a : Fin (n + 2) ↦
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one t j hj))
    (((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut t).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up j⟩).app (Opposite.op ⦋d⦌) R) k

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
