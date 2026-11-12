module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyProduct
public import SerrePositivity.KST.Spectra.PointedHomotopy

/-!
概要：点つき射の正次数ホモトピー群の関手性と直積への射の分解。
方針：基点保存の証明を共通化し、二つの射影の識別性を使う。
規約：群の添字 n は通常の次数 n+1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。loop の積の群への作用。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき Kan 複体の直積の underlying は Kan。
方針：ホーンを成分ごとに充填する通常の直積の補題を適用する。
規約：基点は直積の基点の組。
使われ方：Goerss–Jardine I §7。点つき直積の誘導群準同型。 -/
instance pointedProd_kanComplex (X Y : PointedSimplicialSet.{u})
    [KanComplex X.right] [KanComplex Y.right] : KanComplex (PointedObject.prod X Y).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prod_kanComplex (X := X.right) (Y := Y.right)

/-- 概要：点つき射が正次数ホモトピー群へ誘導する群準同型。
方針：基点を保つ標準の等式を通常の誘導準同型へ渡す。
規約：次数は n+1。
使われ方：Goerss–Jardine I §7。群の合成と積の射の共通表記。 -/
def pointedGroupMap {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (n : ℕ) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right n X.basepoint →* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)

/-- 概要：点つき射の誘導群準同型は恒等射を保つ。
方針：通常の恒等法則を使う。
規約：次数は n+1。
使われ方：Goerss–Jardine I §7。積の射の単位則の群での計算。 -/
@[simp]
theorem pointedGroupMap_id (X : PointedSimplicialSet.{u}) [KanComplex X.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right n X.basepoint) :
    pointedGroupMap n (𝟙 X) a = a :=
  DFunLike.congr_fun _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id a

/-- 概要：点つき射の誘導群準同型は合成を保つ。
方針：通常の合成法則と基点保存の証明の一意性を使う。
規約：全ての対象は Kan。
使われ方：Goerss–Jardine I §7。射影と軸の合成の計算。 -/
theorem pointedGroupMap_comp {X Y Z : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] [KanComplex Z.right]
    (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right n X.basepoint) :
    pointedGroupMap n (f ≫ g) a = pointedGroupMap n g (pointedGroupMap n f a) :=
  DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp f.right _ g.right _ _) a

/-- 概要：零射は正次数の群の全ての元を単位元へ送る。
方針：基点を経由する零射を定数射へ書き直す。
規約：基点保存の証明は証明の一意性で同定する。
使われ方：Goerss–Jardine I §7。直積の二つの軸の計算。 -/
@[simp]
theorem pointedGroupMap_zero (X Y : PointedSimplicialSet.{u})
    [KanComplex X.right] [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right n X.basepoint) :
    pointedGroupMap n (0 : X ⟶ Y) a = 1 := by
  dsimp only [pointedGroupMap]
  simp only [PointedObject.zero_right, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const (n + 1) _ a

/-- 概要：点つき直積の正次数の群の元は射影の像から識別できる。
方針：通常の単体集合の直積の識別補題を基点の組へ適用する。
規約：基点は直積の指定した基点。
使われ方：Goerss–Jardine I §7。直積の軸による分解。 -/
theorem pointedGroupProd_injective (X Y : PointedSimplicialSet.{u})
    [KanComplex X.right] [KanComplex Y.right] (n : ℕ) :
    Function.Injective ((pointedGroupMap n (PointedObject.prodFst X Y)).prod
      (pointedGroupMap n (PointedObject.prodSnd X Y))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prod_map_injective n X.basepoint Y.basepoint

/-- 概要：直積への射の誘導像は二つの軸の誘導像の積である。
方針：射影に沿って二つの像を比較し、直積の群の識別性を使う。
規約：群の次数は n+1、三つの対象は Kan。
使われ方：Goerss–Jardine I §7。二変数の積の射の群での作用。 -/
theorem pointedGroupMap_prodLift {A X Y : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex X.right] [KanComplex Y.right]
    (n : ℕ) (f : A ⟶ X) (g : A ⟶ Y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup A.right n A.basepoint) :
    pointedGroupMap n (PointedObject.prodLift f g) a =
      pointedGroupMap n (PointedObject.axisLeft X Y) (pointedGroupMap n f a) *
        pointedGroupMap n (PointedObject.axisRight X Y) (pointedGroupMap n g a) := by
  apply pointedGroupProd_injective X Y n
  apply Prod.ext
  · change pointedGroupMap n (PointedObject.prodFst X Y)
      (pointedGroupMap n (PointedObject.prodLift f g) a) =
        pointedGroupMap n (PointedObject.prodFst X Y) (_ * _)
    simp only [map_mul, ← pointedGroupMap_comp, Category.assoc, Category.comp_id,
      comp_zero, PointedObject.prodLift_fst, PointedObject.axisLeft, PointedObject.axisRight,
      pointedGroupMap_zero, mul_one]
  · change pointedGroupMap n (PointedObject.prodSnd X Y)
      (pointedGroupMap n (PointedObject.prodLift f g) a) =
        pointedGroupMap n (PointedObject.prodSnd X Y) (_ * _)
    simp only [map_mul, ← pointedGroupMap_comp, Category.assoc, Category.comp_id,
      comp_zero, PointedObject.prodLift_snd, PointedObject.axisLeft, PointedObject.axisRight,
      pointedGroupMap_zero, one_mul]

end

end SerrePositivity.KST.Spectra
