module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeFiberEquivalence

/-!
概要：宇宙の持ち上げによるホーンの相対持ち上げ性と left fibration 性の保存。
方針：各ホーン面と底の simplex を元の宇宙へ戻し、相対充填を再び持ち上げる。
規約：異なる宇宙間の単体集合の射は使わず、Yoneda の同値で値を移す。
使われ方：HTT 4.2.4.1 の weighted nerve と coherent cone の切断空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：標準単体からの射の宇宙を戻す操作は後合成と可換。
方針：Yoneda の同値で両辺を評価して ULift の値を計算する。
規約：射 p は元の宇宙の単体集合間の射。
使われ方：HTT 4.2.4.1 の相対ホーン充填を元の宇宙に降ろす。 -/
lemma uliftSimplexHomDown_post {E B : SSet.{u}} (p : E ⟶ B) {n : ℕ}
    (a : (Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown (a ≫ (SSet.uliftFunctor.{v, u}).map p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown a ≫ p := by
  apply SSet.yonedaEquiv.injective
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown, Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
  rfl

/-- 概要：指定したホーンの相対持ち上げ性は宇宙の持ち上げで保存される。
方針：ホーンの面を戻して貼り合わせ、元の相対充填の simplex を持ち上げる。
規約：全ホーンの持ち上げ性ではなく、指定した n・i の性質だけを仮定する。
使われ方：HTT 4.2.4.1 の left fibration の宇宙の調整。 -/
lemma ulift_hasLiftingProperty_horn {E B : SSet.{u}} (p : E ⟶ B)
    (n : ℕ) (i : Fin (n + 2)) [HasLiftingProperty (horn.{u} (n + 1) i).ι p] :
    HasLiftingProperty (horn.{max u v} (n + 1) i).ι ((SSet.uliftFunctor.{v, u}).map p) := by
  constructor
  intro a b sq
  let f := fun j hj ↦ horn.ι i j hj ≫ a
  have hf : horn.IsCompatible f := horn.IsCompatible.of_hom a
  have hF : horn.IsCompatible (fun j hj ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown (f j hj)) := by
    cases n with
    | zero => trivial
    | succ n =>
      intro j k hj hk hjk
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown_face, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown_face, hf j k hj hk hjk]
  let a₀ := hF.desc
  let b₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown b
  have sq₀ : CommSq a₀ (horn.{u} (n + 1) i).ι p b₀ := by
    constructor
    apply horn.hom_ext'
    intro j hj
    change horn.ι i j hj ≫ hF.desc ≫ p = horn.ι i j hj ≫ (horn (n + 1) i).ι ≫ b₀
    rw [← Category.assoc, horn.IsCompatible.ι_desc, horn.ι_ι_assoc]
    rw [← uliftSimplexHomDown_post, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown_face]
    apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown
    dsimp only [f]
    rw [Category.assoc, sq.w, horn.ι_ι_assoc]
  let φ := sq₀.lift
  have hφ (j : Fin (n + 2)) (hj : j ≠ i) :
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown (f j hj) := by
    rw [← horn.ι_ι_assoc i j hj]
    change horn.ι i j hj ≫ (horn (n + 1) i).ι ≫ sq₀.lift = _
    rw [sq₀.fac_left]
    exact hF.ι_desc j hj
  refine CommSq.HasLift.mk' {
    l := SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv φ))
    fac_left := ?_
    fac_right := ?_ }
  · apply horn.hom_ext'
    intro j hj
    rw [horn.ι_ι_assoc]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change ULift.up (E.δ j (SSet.yonedaEquiv φ)) = SSet.yonedaEquiv (f j hj)
    apply ULift.ext
    have h := congrArg SSet.yonedaEquiv (hφ j hj)
    rw [stdSimplex.yonedaEquiv_δ_comp] at h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown, Equiv.apply_symm_apply] using h
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change ULift.up (p.app (Opposite.op ⦋n + 1⦌) (SSet.yonedaEquiv φ)) =
      SSet.yonedaEquiv b
    apply ULift.ext
    have h := congrArg SSet.yonedaEquiv sq₀.fac_right
    rw [SSet.yonedaEquiv_comp] at h
    simpa only [b₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown, Equiv.apply_symm_apply] using h

/-- 概要：left fibration の宇宙の持ち上げは left fibration。
方針：最後以外の各ホーンについて相対持ち上げ性の保存を使う。
規約：標的の quasicategory 性や Kan 性は要求しない。
使われ方：HTT 4.2.4.1 の持ち上げた weighted nerve の切断空間の比較。 -/
instance leftFibration_uliftFunctor_map {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration ((SSet.uliftFunctor.{v, u}).map p) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      have : HasLiftingProperty (horn.{u} (n + 1) i).ι p :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
      exact ulift_hasLiftingProperty_horn p n i

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
