module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.RelativeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence

/-!
概要：cocartesian 標的への全相対 Hom の制限は、任意の底上の前合成同値に対して同値。
方針：単射の場合の全境界充填を、可逆な写像円柱の二つの包含と収縮で一般化する。
規約：標的の cocartesian 性から持ち上げ条件を証明し、追加の instance 仮定を置かない。
使われ方：universal scaffold の全相対 Hom の制限と、cocartesian 部分への同値の移送。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：単射な底上の前合成同値は相対関手空間の前合成同値を与える。
方針：底の可換性を標準の図式の表示に揃え、単射による相対制限と同型を合成する。
規約：元の二つの定義域は quasicategory でなくてもよい。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の比較の単射の場合。 -/
lemma relativeFunctorOverPre_isPrecompositionEquivalence_of_cocartesian_of_mono
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : Over B} (f : a ⟶ b) [Mono f.left] (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) := by
  let a' : Over B := Over.mk (f.left ≫ b.hom)
  let g : a' ⟶ b := Over.homMk f.left rfl
  let e : a ≅ a' := Over.isoMk (Iso.refl a.left) (by
    change (𝟙 a.left) ≫ f.left ≫ b.hom = a.hom
    rw [Category.id_comp, f.w])
  have hfg : f = e.hom ≫ g := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp f.left).symm
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p g) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_trivialKanFibration_of_cocartesian p b.hom f.left hf
  rw [hfg, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p g)).isPrecompositionEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverFunctor p).mapIso e.op))

/-- 概要：底上の前合成同値は相対関手空間の前合成同値を与える。
方針：可逆な写像円柱の二つの単射と底上の収縮を使い、単射の場合から二対三則で導く。
規約：比較射の単射性も定義域の quasicategory 性も要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、scaffold の底上の span による相対写像空間の比較。 -/
lemma relativeFunctorOverPre_isPrecompositionEquivalence_of_cocartesian
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : Over B} (f : a ⟶ b) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) := by
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderOut f.left
  let m : Over B := Over.mk (r ≫ b.hom)
  let j : a ⟶ m := Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f.left) (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f.left ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderOut f.left ≫ b.hom) = a.hom
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn_out, f.w])
  let r' : m ⟶ b := Over.homMk r rfl
  let s : b.left ⟶ m.left := pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint a.left false) f.left
  have : Mono s := Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout _ _)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence s :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint a.left false).of_isPushout
      (IsPushout.of_hasPushout _ _)
  have hsr : s ≫ r = 𝟙 b.left := pushout.inr_desc _ _ _
  let s' : b ⟶ m := Over.homMk s (by
    change s ≫ (r ≫ b.hom) = b.hom
    rw [← Category.assoc, hsr, Category.id_comp])
  have hsr' : s' ≫ r' = 𝟙 b := by
    apply Over.OverMorphism.ext
    exact hsr
  have hjr : j ≫ r' = f := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn_out f.left
  have hs' := relativeFunctorOverPre_isPrecompositionEquivalence_of_cocartesian_of_mono p s' hs
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p r') := by
    apply hs'.cancel_right
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp, hsr', _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  have hj := relativeFunctorOverPre_isPrecompositionEquivalence_of_cocartesian_of_mono p j
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn f.left).mp hf)
  have h := hr.comp hj
  rwa [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp, hjr] at h

/-- 概要：底上の前合成同値は cocartesian fibration への相対写像空間の quasicategory の同値を与える。
方針：相対関手空間の Kan 性と前合成同値の検出を使う。
規約：比較射の単射性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の写像空間の比較。 -/
lemma relativeFunctorOverPre_isQCatEquivalence_of_cocartesian
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : Over B} (f : a ⟶ b) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) :=
  (relativeFunctorOverPre_isPrecompositionEquivalence_of_cocartesian p f hf).isQCatEquivalence

/-- 概要：任意の前合成同値による相対関手空間の制限は quasicategory の同値。
方針：底を前合成した標準の Over 圏の射に一般の比較を適用する。
規約：p の底は quasicategory、i の定義域と終域は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、scaffold の比較を相対関手空間で使う。 -/
lemma relativeFunctorPre_isQCatEquivalence_of_cocartesian
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (a : A ⟶ B) (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) :=
  relativeFunctorOverPre_isQCatEquivalence_of_cocartesian p
    (Over.homMk (U := Over.mk (i ≫ a)) (V := Over.mk a) i rfl) hi

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
