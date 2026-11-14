module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniverseLeftFibration

/-!
概要：宇宙の持ち上げによる left fibration 性の反映。
方針：小さいホーンの各面を持ち上げ、得た充填単体を元の宇宙へ戻す。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening の射影の充填性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：標準単体からの射を大きい宇宙へ持ち上げる。
方針：Yoneda の同値で対応する単体を ULift する。
規約：始域の標準単体も大きい宇宙へ移す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さいホーンの面を大きい充填問題へ移す。 -/
def uliftSimplexHomUp {X : SSet.{u}} {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X :=
  SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv f))

/-- 概要：標準単体からの射を持ち上げて戻すと元の射。
方針：Yoneda の同値と ULift の往復を計算する。
規約：任意の次数を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対充填の境界条件を元の宇宙へ戻す。 -/
lemma uliftSimplexHomDown_up {X : SSet.{u}} {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown (uliftSimplexHomUp.{u, v} f) = f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown, uliftSimplexHomUp, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]

/-- 概要：標準単体からの射の持ち上げは面への制限と可換。
方針：Yoneda の同値で評価し、同じ面の単体作用を比較する。
規約：全ての面番号を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げたホーンの面の互換性。 -/
lemma uliftSimplexHomUp_face {X : SSet.{u}} {n : ℕ} (f : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ uliftSimplexHomUp.{u, v} f = uliftSimplexHomUp (stdSimplex.δ j ≫ f) := by
  apply SSet.yonedaEquiv.injective
  simp only [uliftSimplexHomUp, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  rfl

/-- 概要：標準単体からの射の持ち上げは後合成と可換。
方針：Yoneda の同値で両辺の単体を計算する。
規約：後合成する射 p は元の宇宙に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、大きい相対ホーンの可換四角形の構成。 -/
lemma uliftSimplexHomUp_post {X Y : SSet.{u}} (p : X ⟶ Y) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) :
    uliftSimplexHomUp.{u, v} f ≫ (SSet.uliftFunctor.{v, u}).map p =
      uliftSimplexHomUp (f ≫ p) := by
  apply SSet.yonedaEquiv.injective
  simp only [uliftSimplexHomUp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 概要：指定ホーンの相対持ち上げ性は宇宙持ち上げから反映される。
方針：全ての面を持ち上げてホーンを貼り合わせ、充填の単体を降ろす。
規約：ホーンの番号は端の番号を含め任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、縮小した射影の left fibration 性。 -/
lemma hasLiftingProperty_horn_of_ulift {E B : SSet.{u}} (p : E ⟶ B)
    (n : ℕ) (i : Fin (n + 2))
    [HasLiftingProperty (horn.{max u v} (n + 1) i).ι ((SSet.uliftFunctor.{v, u}).map p)] :
    HasLiftingProperty (horn.{u} (n + 1) i).ι p := by
  constructor
  intro a b sq
  let f := fun j hj ↦ horn.ι i j hj ≫ a
  have hf : horn.IsCompatible f := horn.IsCompatible.of_hom a
  have hF : horn.IsCompatible (fun j hj ↦ uliftSimplexHomUp.{u, v} (f j hj)) := by
    cases n with
    | zero => trivial
    | succ n =>
      intro j k hj hk hjk
      rw [uliftSimplexHomUp_face, uliftSimplexHomUp_face, hf j k hj hk hjk]
  have sq' : CommSq hF.desc (horn.{max u v} (n + 1) i).ι
      ((SSet.uliftFunctor.{v, u}).map p) (uliftSimplexHomUp b) := by
    constructor
    apply horn.hom_ext'
    intro j hj
    rw [← Category.assoc, horn.IsCompatible.ι_desc, uliftSimplexHomUp_post,
      horn.ι_ι_assoc, uliftSimplexHomUp_face]
    apply congrArg uliftSimplexHomUp
    change (horn.ι i j hj ≫ a) ≫ p = stdSimplex.δ j ≫ b
    rw [Category.assoc, sq.w, horn.ι_ι_assoc]
  refine CommSq.HasLift.mk' {
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown sq'.lift
    fac_left := ?_
    fac_right := ?_ }
  · apply horn.hom_ext'
    intro j hj
    rw [horn.ι_ι_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown_face]
    have h : stdSimplex.δ j ≫ sq'.lift = uliftSimplexHomUp (f j hj) := by
      rw [← horn.ι_ι_assoc i j hj, sq'.fac_left]
      exact hF.ι_desc j hj
    rw [h, uliftSimplexHomDown_up]
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftSimplexHomDown_post, sq'.fac_right,
      uliftSimplexHomDown_up]

/-- 概要：宇宙を持ち上げた射が left fibration なら元の射も left fibration。
方針：最後以外の各ホーンの相対持ち上げ性を反映する。
規約：充填の選択は構造に含めない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい全空間による unstraightening の束縛。 -/
lemma leftFibration_of_ulift {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration ((SSet.uliftFunctor.{v, u}).map p)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      have : HasLiftingProperty (horn.{max u v} (n + 1) i).ι
          ((SSet.uliftFunctor.{v, u}).map p) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
      exact hasLiftingProperty_horn_of_ulift p n i

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
