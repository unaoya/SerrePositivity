module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.DGOdotQuotient
public import SerrePositivity.KST.SConstruction.DGAlgebraRightEndOrientation
public import SerrePositivity.DifferentialGraded.Functor.Closed

/-! # 元の実対角商 End の dg 代数と元の右代数射
概要：元の商 End を右加群の向きに代数化し、元の右代数からの単位・積保存射を構成する。
方針：Sp の dgEndAlgebra と元の dg 射の反転を使い、二重交換で元の右代数を回収する。
規約：LT の lax pullback 同定と生成性は未主張。使われ方：具体的 dg ⊙ の代数候補。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
open scoped MonObj
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Q" => DGOdotQuotientEnd R d

/-- 同じ実対角商の指定 End を、右加群の向きへ揃えた実 dg 代数。 -/
def dgOdotAlgebra : Mon (Complex R) :=
  LocalizingInvariants.dgEndAlgebra R (Q)ᵒᵖ (Opposite.op EndomorphismObject.point)

/-- 元の右代数から同じ実商 End 代数への、元の dg End 射を使う代数射。 -/
def dgOdotRightMap : d.right ⟶ dgOdotAlgebra R d :=
  (dgAlgebraRightEndIso R d.right (dgOdotInputRightPoint R d)).hom ≫
    LocalizingInvariants.dgEndAlgebraMap R (EndomorphismObject (dgOdotInputRightPoint R d))ᵒᵖ
      (dgOdotRightEndMap R d).op (Opposite.op EndomorphismObject.point)

/-- 元の右代数射の基礎鎖写像は、同じ元の右 End 射の全 Hom 作用そのもの。 -/
lemma dgOdotRightMap_hom : (dgOdotRightMap R d).hom =
    (dgOdotRightEndMap R d).map EndomorphismObject.point EndomorphismObject.point := by
  change (𝟙 d.right.X) ≫
    (dgOdotRightEndMap R d).map EndomorphismObject.point EndomorphismObject.point = _
  exact Category.id_comp _

/-- 同じ実 dg 代数の単位は、元の商 End の閉単位そのもの。 -/
lemma dgOdotAlgebra_one : η[(dgOdotAlgebra R d).X] =
    eId (Complex R) (EndomorphismObject.point : Q) := rfl

/-- 同じ実 dg 代数の積は、元の forward 合成へ Koszul 交換を一回合成したもの。 -/
lemma dgOdotAlgebra_mul : μ[(dgOdotAlgebra R d).X] =
    (β_ (dgOdotAlgebra R d).X (dgOdotAlgebra R d).X).hom ≫
      eComp (Complex R) (EndomorphismObject.point : Q) EndomorphismObject.point
        EndomorphismObject.point := rfl

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Construction §1 ⊙" (partial := component) "仮定：可換基礎環上の dg 圏、指定対角・左零・右代表（Lean が強い）。結論：(0,b,0) の dg 商での自己準同型とその dg 代数模型。一般の E₁ 環スペクトル版との比較は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotAlgebra
