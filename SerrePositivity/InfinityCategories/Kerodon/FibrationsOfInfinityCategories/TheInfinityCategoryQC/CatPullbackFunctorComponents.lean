module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackFunctor

/-!
概要：引き戻し候補と関手単体集合の比較の二射影・指定 path の計算。
方針：lift の射影公式と curry・uncurry の逆条件を適用する。
規約：全ての式は全次数での単体集合の射の厳密な等式。
使われ方：全試験対象の関手空間比較の逆条件の証明。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory C]

/-- 概要：関手空間比較の第一射影は元の第一射影の後合成。
方針：指定 path の lift の第一射影を計算する。
規約：試験 K は任意。
使われ方：第一の関手空間への射影の一致。 -/
lemma catPullbackFunctorMap_fst (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap K p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst ((ihom K).map p) ((ihom K).map q) =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift_fst ..

/-- 概要：関手空間比較の第二射影は元の第二射影の後合成。
方針：指定 path の lift の第二射影を計算する。
規約：試験 K は任意。
使われ方：第二の関手空間への射影の一致。 -/
lemma catPullbackFunctorMap_snd (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap K p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd ((ihom K).map p) ((ihom K).map q) =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift_snd ..

/-- 概要：関手空間比較の path 成分は元の族を内部 Hom と交換したもの。
方針：指定 path の lift の path 射影を計算する。
規約：元の path の全ての単体を保つ。
使われ方：比較の合成と指定可換性の一致。 -/
lemma catPullbackFunctorMap_path (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap K p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath ((ihom K).map p) ((ihom K).map q) =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso K C).inv :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift_path ..

/-- 概要：逆向きの関手空間比較の第一射影は関手空間側の第一射影。
方針：uncurry して元の lift の第一射影を計算する。
規約：内部 Hom の等式として比較する。
使われ方：比較の第一成分での逆条件。 -/
lemma catPullbackFunctorInv_fst (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv K p q ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst ((ihom K).map p) ((ihom K).map q) := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift_fst]

/-- 概要：逆向きの関手空間比較の第二射影は関手空間側の第二射影。
方針：uncurry して元の lift の第二射影を計算する。
規約：内部 Hom の等式として比較する。
使われ方：比較の第二成分での逆条件。 -/
lemma catPullbackFunctorInv_snd (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv K p q ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd ((ihom K).map p) ((ihom K).map q) := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift_snd]

/-- 概要：逆向きの関手空間比較は指定 path を交換の順射で戻す。
方針：uncurry して元の lift の path 成分を計算する。
規約：両端だけでなく指定可逆 path 自体を比較する。
使われ方：比較の path 成分での逆条件。 -/
lemma catPullbackFunctorInv_path (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv K p q ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath ((ihom K).map p) ((ihom K).map q) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso K C).hom := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift_path]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
