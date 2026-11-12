module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Module.TransferInstance

/-! # 実際の右 pinched Hom の線形構造

概要：右 pinched 写像空間の実際の各単体の集合に加群構造を与える。
方針：N4 の線形模型との同型で加群構造を移し、全ての面と退化の線形性を得る。
規約：対象の宇宙が大きい場合も実際の pinched Hom を用いる。
使われ方：右写像空間の正規化 Moore 複体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory S D] (x y : D)

/-- 概要：実際の pinched 単体と宇宙を持ち上げた線形単体の全単射。
方針：N4 の単体的同型を各次数で取る。
規約：逆方向を取る。使われ方：線形構造の転送。 -/
def pinchedHomCoordinateEquiv (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y).obj n ≃
      ULift.{v} ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y).obj n) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := S) x y).app n).toEquiv.symm

/-- 概要：実際の右 pinched 単体の可換加法群構造。
方針：線形座標から転送する。
規約：N4 の零単体を零とする。使われ方：写像空間の線形化。 -/
instance pinchedHomAddCommGroup (n : SimplexCategoryᵒᵖ) :
    AddCommGroup ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y).obj n) :=
  (pinchedHomCoordinateEquiv x y n).addCommGroup

/-- 概要：実際の右 pinched 単体の係数加群構造。
方針：座標の加法同値に沿って係数作用を転送する。
規約：環 S 上。使われ方：Moore 正規化の入力。 -/
instance pinchedHomModuleStructure (n : SimplexCategoryᵒᵖ) :
    Module S ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y).obj n) :=
  (pinchedHomCoordinateEquiv x y n).addEquiv.module S

/-- 概要：実際の単体と線形座標の間の線形同値。
方針：転送された構造による線形同値を取る。
規約：台写像は N4 の成分回収。使われ方：面・退化の線形化。 -/
def pinchedHomCoordinateLinearEquiv (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y).obj n ≃ₗ[S]
      ULift.{v} ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y).obj n) :=
  (pinchedHomCoordinateEquiv x y n).addEquiv.linearEquiv S

/-- 概要：座標比較を加群圏の同型として固定する。
方針：宇宙持ち上げ関手の対象を終域として指定する。
規約：型と加群構造の両方を一致させる。使われ方：単体的関手の共役。 -/
def pinchedHomCoordinateModuleIso (n : SimplexCategoryᵒᵖ) :
    ModuleCat.of S ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y).obj n) ≅
      (ModuleCat.uliftFunctor.{v} S).obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y).obj n) :=
  (pinchedHomCoordinateLinearEquiv x y n).toModuleIso

/-- 概要：実際の右 pinched Hom の各単体を加群としてまとめる。
方針：座標の単体的加群の射を線形同値で共役する。
規約：各項の台集合は実際の pinched 単体。使われ方：正規化 Moore 複体。 -/
def pinchedHomModule : SimplicialObject (ModuleCat.{max u v} S) where
  obj n := ModuleCat.of S ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y).obj n)
  map {m n} f :=
    (pinchedHomCoordinateModuleIso x y m).hom ≫
      (ModuleCat.uliftFunctor.{v} S).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y).map f) ≫
        (pinchedHomCoordinateModuleIso x y n).inv
  map_id n := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y).map_id,
      (ModuleCat.uliftFunctor.{v} S).map_id, Category.id_comp]
    exact (pinchedHomCoordinateModuleIso x y n).hom_inv_id
  map_comp f g := by
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- 概要：実際の pinched 単体的加群は N4 の線形模型の宇宙持ち上げと同型である。
方針：各次数の座標の線形同型を取る。
規約：面・退化との自然性を含む。使われ方：Moore 複体の計算模型。 -/
def pinchedHomModuleCoordinateIso : pinchedHomModule x y ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := S) x y ⋙ ModuleCat.uliftFunctor.{v} S :=
  NatIso.ofComponents (fun n => (pinchedHomCoordinateModuleIso x y n))
    (by
      intro m n f
      change (_ ≫ _ ≫ (pinchedHomCoordinateModuleIso x y n).inv) ≫
        (pinchedHomCoordinateModuleIso x y n).hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.comp_map])

/-- 概要：線形化を忘れると実際の右 pinched 写像空間となる。
方針：座標同型と N4 の単体的同型を合成する。
規約：全次数の自然同型。使われ方：小さい模型だけを写像空間とみなさないための比較。 -/
def pinchedHomModuleForgetIso : pinchedHomModule x y ⋙ forget (ModuleCat.{max u v} S) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y :=
  Functor.isoWhiskerRight (pinchedHomModuleCoordinateIso x y) (forget _) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := S) x y

/-- 概要：忘却後の比較は実際の pinched 単体を変えない。
方針：N4 の同型の逆射と順射を打ち消す。
規約：実際の単体の等式。使われ方：線形構造が右写像空間上に載っていることの確認。 -/
lemma pinchedHomModuleForgetIso_apply (n : SimplexCategoryᵒᵖ)
    (s : (pinchedHomModule (S := S) x y).obj n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso x y).hom.app n s = s := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := S) x y).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := S) x y).hom).app n s = s
  rw [Iso.inv_hom_id]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
