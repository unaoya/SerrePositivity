module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseFunctorPrecomposition

/-!
概要：変動する添字上の関手の全空間に標的の射による後合成を定義する。
方針：各底単体の図式に同じ標的の射を後合成する。
規約：底と局所形を変更しない。
使われ方：相対 Kan の組み立てに用いる全空間の相対比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：各底単体の図式を標的の射で後合成する。
方針：依存和の第一成分を保ち、第二成分だけを後合成する。
規約：パラメータは任意。
使われ方：全空間の後合成の単体ごとの作用。 -/
def fiberwiseFunctorPostSimplex {B T D E : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (U : D ⟶ E) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F E T := ⟨s.1, s.2 ≫ U⟩

/-- 概要：標的への後合成はパラメータの制限と可換。
方針：依存和の底を固定して射の結合律を使う。
規約：局所形の保存性や充填性は不要。
使われ方：後合成を単体集合の射にまとめる。 -/
lemma fiberwiseFunctorPostSimplex_restrict {B T V D E : SSet.{u}}
    (F : Over B ⥤ SSet.{u}) (U : D ⟶ E) (i : T ⟶ V)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D V) :
    fiberwiseFunctorPostSimplex F U (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorRestrict F D i s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorRestrict F E i (fiberwiseFunctorPostSimplex F U s) := by
  rcases s with ⟨σ, h⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  exact Category.assoc _ _ _

/-- 概要：標的への後合成が誘導する関手の族の全空間の射。
方針：底単体ごとの後合成と制限との可換性をまとめる。
規約：標的の射は任意。
使われ方：相対的な普遍余錐の全空間の構成。 -/
def fiberwiseFunctorPostcomp {B D E : SSet.{u}} (F : Over B ⥤ SSet.{u}) (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F E where
  app _ := ↾fiberwiseFunctorPostSimplex F U
  naturality {m n} i := by
    apply ConcreteCategory.hom_ext
    intro s
    exact fiberwiseFunctorPostSimplex_restrict F U (stdSimplex.map i.unop) s

/-- 概要：関手の族の後合成は底への射影を保つ。
方針：各単体の第一成分を変えないことを使う。
規約：底への射の厳密な等式。
使われ方：各頂点の fiber への後合成の制限。 -/
lemma fiberwiseFunctorPostcomp_projection {B D E : SSet.{u}}
    (F : Over B ⥤ SSet.{u}) (U : D ⟶ E) :
    fiberwiseFunctorPostcomp F U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F E =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D := rfl

/-- 概要：図式を後合成してから作る族は、元の族の後合成に一致する。
方針：各単体で後合成とパラメータ制限の可換性を使う。
規約：元の図式は任意のパラメータ上にある。
使われ方：底の指定された図式を持ち上げ問題へ写す。 -/
lemma fiberwiseFunctorCurry_postcomp {B A D E : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (U : D ⟶ E) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry F (fiberwiseFunctorPostSimplex F U s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry F s ≫ fiberwiseFunctorPostcomp F U := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact (fiberwiseFunctorPostSimplex_restrict F U (SSet.yonedaEquiv.symm x) s).symm

/-- 概要：局所形の前合成と標的への後合成は可換。
方針：底単体の各図式で射の結合律を使う。
規約：局所形の自然変換は任意。
使われ方：全空間の相対比較の可換四角形。 -/
lemma fiberwiseFunctorPre_postcomp {B D E : SSet.{u}} {F G : Over B ⥤ SSet.{u}}
    (α : F ⟶ G) (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorPre (D := D) α ≫ fiberwiseFunctorPostcomp F U =
      fiberwiseFunctorPostcomp G U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorPre (D := E) α := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, h⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  exact Category.assoc _ _ _

/-- 概要：恒等射による後合成は全空間の恒等射。
方針：各図式の射の右単位律を使う。
規約：底と局所形は任意。
使われ方：標的に関する関手性。 -/
lemma fiberwiseFunctorPostcomp_id {B D : SSet.{u}} (F : Over B ⥤ SSet.{u}) :
    fiberwiseFunctorPostcomp F (𝟙 D) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, h⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  exact Category.comp_id h

/-- 概要：標的の二つの射の後合成は全空間でも合成となる。
方針：各底単体で射の結合律を使う。
規約：三つの標的に充填性を仮定しない。
使われ方：標的に関する関手性。 -/
lemma fiberwiseFunctorPostcomp_comp {B D E H : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (U : D ⟶ E) (V : E ⟶ H) :
    fiberwiseFunctorPostcomp F (U ≫ V) =
      fiberwiseFunctorPostcomp F U ≫ fiberwiseFunctorPostcomp F V := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, h⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  exact (Category.assoc h U V).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
