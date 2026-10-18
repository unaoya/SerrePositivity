module

public import SerrePositivity.KST.Spectra.PointedMappingParameters
public import SerrePositivity.KST.Spectra.PointedIntervalAnodyne
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
概要：anodyne な基点包含からの点つき Hom の全境界充填。
方針：pushout-product と指数の随伴で全ての単射に対する右持ち上げ性を移す。
規約：終対象への射の RLP として全境界充填を表す。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3。path の零次数の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：anodyne な射による Kan 標的への指数の制限は全ての単射に RLP を持つ。
方針：単射との pushout-product の anodyne 性とパラメータ付き随伴を使う。
規約：全ての単射についての右持ち上げ性を述べる。
使われ方：Kerodon §3.1.3、Goerss–Jardine I §7。path space の全境界充填。 -/
theorem anodyne_pre_rlp_monomorphisms {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) (Y : SSet.{u}) [KanComplex Y] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app Y) := by
  intro S T j hj
  let : Mono j := hj
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let sq₁₃ := Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom
    i (terminal.from Y) terminalIsTerminal
  change HasLiftingProperty j sq₁₃.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂ sq₁₃]
  exact (anodyneExtensions_pushoutObjObjι' sq₁₂ hi) (terminal.from Y)
    ((HomotopicalAlgebra.fibration_iff _).mp inferInstance)

/-- 概要：anodyne な基点包含を持つ源からの点つき Hom は全ての単射に RLP を持つ。
方針：指数の制限の RLP を基点条件の等化子へ移す。
規約：結論は全ての単射に対する終対象への射の RLP。
使われ方：Kerodon §3.1.3、Goerss–Jardine I §7。path の全境界充填。 -/
theorem basedHom_terminal_rlp_monomorphisms (X Y : PointedSimplicialSet.{u})
    (hx : anodyneExtensions X.hom) [KanComplex Y.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from (PointedObject.basedHom X Y).right) := by
  intro A B j hj
  let : HasLiftingProperty j (PointedObject.homRestriction X Y) :=
    anodyne_pre_rlp_monomorphisms X.hom hx Y.right j hj
  constructor
  intro a b _
  let sq : CommSq (a ≫ PointedObject.basedHomι X Y) j (PointedObject.homRestriction X Y)
      (toUnit B ≫ PointedObject.homBasepoint PointedObject.point Y) := by
    constructor
    rw [Category.assoc, PointedObject.basedHomι_condition]
    change a ≫ PointedObject.basedHomι X Y ≫
      (toUnit _ ≫ PointedObject.homBasepoint PointedObject.point Y) = _
    simp only [comp_toUnit_assoc]
  have heq : sq.lift ≫ PointedObject.homRestriction X Y =
      sq.lift ≫ PointedObject.homConstant X Y := by
    rw [sq.fac_right]
    change _ = sq.lift ≫ (toUnit _ ≫ PointedObject.homBasepoint PointedObject.point Y)
    simp only [comp_toUnit_assoc]
  let l : B ⟶ (PointedObject.basedHom X Y).right :=
    equalizer.lift (f := PointedObject.homRestriction X Y) (g := PointedObject.homConstant X Y)
      sq.lift heq
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := Subsingleton.elim _ _ }⟩⟩
  apply (cancel_mono (PointedObject.basedHomι X Y)).mp
  change (j ≫ l) ≫ equalizer.ι _ _ = _
  rw [Category.assoc, equalizer.lift_ι]
  exact sq.fac_left

end

end SerrePositivity.KST.Spectra
