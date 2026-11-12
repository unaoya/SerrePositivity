module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedMapBoundaryLift

/-!
概要：成分ごとの自明 Kan 自然変換の weighted nerve 自体が自明 Kan fibration。
方針：零次元は一つの係数の切断、正次元は最後の係数の相対境界充填を使う。
規約：係数の Kan 性は不要。使われ方：自然な twisted-arrow 比較の全空間の同値。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {F G : I ⥤ SSet.{u}}
  (η : F ⟶ G) [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app i)]

/-- 同じ weighted 比較は、元の全ての頂点を厳密に持ち上げる。 -/
lemma weightedMap_surjective_vertex :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η).app (Opposite.op ⦋0⦌)) := by
  intro s
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (η.app (s.1.obj 0))
  let φ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight 0 ⟶ s.1 ⋙ F :=
    { app i := by
        have hi : i = 0 := Fin.fin_one_eq_zero i
        subst i
        exact s.2.app 0 ≫ g
      naturality i j f := by
        have hi : i = 0 := Fin.fin_one_eq_zero i
        have hj : j = 0 := Fin.fin_one_eq_zero j
        subst i
        subst j
        have hf : f = 𝟙 (0 : Fin 1) := Subsingleton.elim _ _
        subst f
        simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }
  refine ⟨⟨s.1, φ⟩, ?_⟩
  change (⟨s.1, φ ≫ Functor.whiskerLeft s.1 η⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G 0) = s
  have he : φ ≫ Functor.whiskerLeft s.1 η = s.2 := by
    apply NatTrans.ext
    funext i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst i
    change (s.2.app 0 ≫ g) ≫ η.app (s.1.obj 0) = s.2.app 0
    rw [Category.assoc, hg]
    exact Category.comp_id _
  exact (congrArg (fun t ↦ (⟨s.1, t⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G 0)) he).trans (Sigma.eta s)

/-- 元の自然変換の全成分が自明 Kan なら、元の weighted 比較自身も自明 Kan。 -/
instance weightedMap_trivialKanFibration : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
      obtain ⟨x, hx⟩ := weightedMap_surjective_vertex η (SSet.yonedaEquiv b)
      refine CommSq.HasLift.mk'
        { l := SSet.yonedaEquiv.symm x
          fac_left := boundary.hom_ext₀
          fac_right := ?_ }
      rw [SSet.yonedaEquiv_symm_comp, hx, SSet.yonedaEquiv.symm_apply_apply]
  | succ n =>
      obtain ⟨H, hH, hη⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_weightedMap_boundary_lift η (SSet.yonedaEquiv b) a (by
        simpa only [SSet.yonedaEquiv.symm_apply_apply] using sq.w)
      refine CommSq.HasLift.mk' { l := H, fac_left := hH, fac_right := ?_ }
      simpa only [SSet.yonedaEquiv.symm_apply_apply] using hη

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
