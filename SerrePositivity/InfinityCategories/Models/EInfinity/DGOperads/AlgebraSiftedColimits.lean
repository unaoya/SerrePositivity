module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraColimits
public import Mathlib.CategoryTheory.Filtered.Final

/-!
模型。文献の定義との比較は後で
# オペラッド代数の sifted・filtered 余極限

概要：Berger–Moerdijk §1 の代数の忘却関手は sifted・filtered 余極限を作る。
方針：有限テンソル冪の保存を、底の余極限の持ち上げに適用する。
規約：零入力演算を含み、入力の代数の cofibrancy は要求しない。
使われ方：生成射の自由像の小対象性と、代数の余極限の表示を構成する。
-/

@[expose] public section

noncomputable section

universe w v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} (J : Type w) [Category.{v} J]

/-- 概要：忘却関手は sifted 余極限を作る（BM §1）。
方針：有限テンソル冪の保存から図式ごとの創出を得る。
規約：底の余極限の存在はこの創出の型には要求しない。
使われ方：底に存在する sifted 余極限を代数へ持ち上げる。 -/
instance forget_createsSiftedColimitsOfShape [IsSifted J] :
    CreatesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) where
  CreatesColimit := inferInstance

/-- 概要：底に存在する sifted 余極限は代数にも存在する（BM §1）。
方針：忘却関手の創出で底の余極限を持ち上げる。
規約：形の対象と射の宇宙は独立。
使われ方：代数の filtered 余極限と reflexive coequalizer の存在を導く。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasColimitsOfShapeOfIsSiftedOfComplex [IsSifted J] [HasColimitsOfShape J (Complex A)] :
    HasColimitsOfShape J P.Algebra :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)

/-- 概要：忘却関手は filtered 余極限を作る（BM §1）。
方針：filtered な形の sifted 性を適用する。
規約：底の余極限の存在は別に供給する。
使われ方：忘却による filtered 余極限の計算と小対象性を与える。 -/
instance forget_createsFilteredColimitsOfShape [IsFiltered J] :
    CreatesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := by
  have : IsSifted J := IsFiltered.isSifted
  infer_instance

/-- 概要：底に存在する filtered 余極限は代数にも存在する（BM §1）。
方針：filtered 余極限の創出を底の存在へ適用する。
規約：元の代数の圏の余極限を仮定しない。
使われ方：自由像の生成射の小対象性の値域を供給する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasColimitsOfShapeOfIsFilteredOfComplex [IsFiltered J] [HasColimitsOfShape J (Complex A)] :
    HasColimitsOfShape J P.Algebra :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
