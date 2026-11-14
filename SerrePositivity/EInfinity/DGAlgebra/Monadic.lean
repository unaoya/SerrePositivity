module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.DGAlgebra.Free
public import SerrePositivity.EInfinity.DGAlgebra.Colimits
public import Mathlib.CategoryTheory.Monad.Monadicity
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# dg モノイドの sifted 余極限とモナド性

概要：忘却が sifted 余極限・分裂 coequalizer を作ることを証明する。
方針：入力関手の保存を底の余極限の持ち上げへ代入し、Beck の判定を使う。
規約：クラスの構成は明示した値とし、大域 instance を追加しない。
使われ方：全余極限と自由生成射の小対象性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R]

/-- 概要：忘却関手は sifted 余極限を作る。
方針：単位と二重・三重テンソルの保存を代入する。
規約：元の代数の余極限の存在は仮定しない。
使われ方：filtered 余極限と reflexive coequalizer。 -/
@[instance_reducible]
def forgetCreatesSiftedColimits (J : Type w) [Category.{v} J] [IsSifted J] :
    CreatesColimitsOfShape J (Mon.forget (Complex R)) where
  CreatesColimit {F} := by
    have := unitInput_preservesColimit (F ⋙ Mon.forget (Complex R))
    have : PreservesColimit (F ⋙ Mon.forget (Complex R)) binaryInput :=
      tensorInput_preservesColimit _ (𝟭 _) (𝟭 _)
    have : PreservesColimit (F ⋙ Mon.forget (Complex R)) ternaryInput :=
      tensorInput_preservesColimit _ binaryInput (𝟭 _)
    exact forgetCreatesColimit F

/-- 概要：底に存在する sifted 余極限は dg 代数にも存在する。
方針：忘却による創出を使う。
規約：形の宇宙は係数環から独立。
使われ方：reflexive coequalizer と余極限構成。 -/
lemma hasSiftedColimits (J : Type w) [Category.{v} J] [IsSifted J]
    [HasColimitsOfShape J (Complex R)] : HasColimitsOfShape J (Mon (Complex R)) := by
  let := forgetCreatesSiftedColimits (R := R) J
  exact hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (Mon.forget (Complex R))

/-- 概要：忘却後に分裂する対の底の coequalizer は任意の入力関手が保つ。
方針：分裂 coequalizer の絶対性を平行対図式の同型で移す。
規約：代数での分裂を要求しない。
使われ方：Beck の分裂対の判定。 -/
lemma splitPair_input_preservesColimit {B C : Mon (Complex R)} (f g : B ⟶ C)
    [(Mon.forget (Complex R)).IsSplitPair f g] (T : Complex R ⥤ Complex R) :
    PreservesColimit (parallelPair f g ⋙ Mon.forget (Complex R)) T := by
  have : HasSplitCoequalizer f.hom g.hom :=
    inferInstanceAs ((Mon.forget (Complex R)).IsSplitPair f g)
  have : PreservesColimit
      (parallelPair ((parallelPair f g ⋙ Mon.forget (Complex R)).map WalkingParallelPairHom.left)
        ((parallelPair f g ⋙ Mon.forget (Complex R)).map WalkingParallelPairHom.right)) T := by
    change PreservesColimit (parallelPair f.hom g.hom) T
    infer_instance
  exact preservesColimit_of_iso_diagram T
    (diagramIsoParallelPair (parallelPair f g ⋙ Mon.forget (Complex R))).symm

/-- 概要：忘却関手は忘却後に分裂する coequalizer を作る。
方針：三入力の絶対保存と底の持ち上げを使う。
規約：同じ元の代数と射を保つ。
使われ方：自由随伴からのモナド性。 -/
@[instance_reducible]
def forgetCreatesSplitCoequalizers :
    Monad.CreatesColimitOfIsSplitPair (Mon.forget (Complex R)) where
  out f g _ := by
    have := splitPair_input_preservesColimit f g (unitInput (R := R))
    have := splitPair_input_preservesColimit f g (binaryInput (R := R))
    have := splitPair_input_preservesColimit f g (ternaryInput (R := R))
    exact forgetCreatesColimit (parallelPair f g)

/-- 概要：元の dg モノイドの忘却はモナド的右随伴。
方針：実自由随伴と分裂 coequalizer の創出へ Beck の判定を適用する。
規約：モデル構造の存在を要求しない。
使われ方：定数図式への随伴を持ち上げる。 -/
@[instance_reducible]
def forgetMonadic : MonadicRightAdjoint (Mon.forget (Complex R)) := by
  let := forgetCreatesSplitCoequalizers (R := R)
  exact Monad.monadicOfCreatesGSplitCoequalizers freeForgetAdjunction

end SerrePositivity.EInfinity.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.7.3.11" (partial := special) "仮定：可換環 R 上の通常の複体圏の厳密な結合 dg 代数（Lean が強い：通常の複体圏の厳密な dg 代数の場合）。結論：厳密な dg 代数から複体への忘却がモナド的となる（この仮定での HA の結論の一部に一致）。色を本質的全射に覆う一般の ∞ オペラッドの制限との比較は含まれない。"] _root_.SerrePositivity.EInfinity.DGAlgebra.forgetMonadic
