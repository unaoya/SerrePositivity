module

public import SerrePositivity.KST.DerivedGeometry.ModuleLocalizationR
public import SerrePositivity.KST.DerivedGeometry.BasicOpenSectionLocalization

/-!
概要：切断の局所化から基本開との交叉上の切断への自然比較。
方針：交叉上で可逆な基本開の定義元の作用に局所化の普遍性を適用する。
規約：比較は全ての開上で定義し、同型性は基本開で別に証明する。
使われ方：TT §3、Toën §3.2 の有限基本開被覆の Čech 各項の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (N : (Spec R).Modules) (a : R)

/--
概要：基本開 D(a) との交叉を取る開集合の関手。
方針：各開 U を U ∩ D(a) に送る。
規約：射は同じ包含関係から与える。
使われ方：TT §3、Toën §3.2 の制限後の Čech 各項。
-/
def basicOpenIntersectionFunctor : (Spec R).Opens ⥤ (Spec R).Opens where
  obj U := U ⊓ basicOpen a
  map f := homOfLE (inf_le_inf (leOfHom f) le_rfl)

/--
概要：U ∩ D(a) 上の切断では a の全ての冪が可逆に作用する。
方針：構造層の基本開上の可逆性を係数加群層の作用へ移す。
規約：任意の O 加群層について述べる。
使われ方：TT §3、Toën §3.2 の切断の局所化の普遍性。
-/
lemma basicOpenIntersection_scalarUnits (U : (Spec R).Opens) :
    ∀ s : Submonoid.powers a, IsUnit (algebraMap R
      (Module.End R ((modulesSpecToSheaf.obj N).obj.obj (.op (U ⊓ basicOpen a)))) s.val) := by
  have h : IsUnit (algebraMap R
      (Module.End R ((modulesSpecToSheaf.obj N).obj.obj (.op (U ⊓ basicOpen a)))) a) :=
    N.isUnit_algebraMap_end_of_le_basicOpen a inf_le_right
  rintro ⟨_, n, rfl⟩
  rw [map_pow]
  exact h.pow n

/--
概要：U 上の切断の a による局所化から U ∩ D(a) 上の切断への線形写像。
方針：制限写像を a の冪の可逆性によって延長する。
規約：U の準コンパクト性や N の準連接性はこの写像の定義に不要。
使われ方：TT §3、Toën §3.2 の Čech 複体の局所化比較。
-/
def sectionLocalizationComparisonAt (U : (Spec R).Opens) :
    (moduleLocalizationR (.powers a)).obj ((modulesSpecToSheaf.obj N).obj.obj (.op U)) ⟶
      (modulesSpecToSheaf.obj N).obj.obj (.op (U ⊓ basicOpen a)) :=
  moduleLocalizationR_lift (.powers a)
    ((modulesSpecToSheaf.obj N).obj.map (homOfLE inf_le_left).op)
    (basicOpenIntersection_scalarUnits N a U)

/--
概要：局所化比較と元の切断の局所化写像の合成は元の制限写像。
方針：局所化の普遍的延長の生成元上の公式を使う。
規約：切断の値の等式を明示する。
使われ方：TT §3、Toën §3.2 の自然性と基本開での同型性。
-/
lemma sectionLocalizationComparisonAt_mk (U : (Spec R).Opens)
    (m : (modulesSpecToSheaf.obj N).obj.obj (.op U)) :
    sectionLocalizationComparisonAt N a U (LocalizedModule.mkLinearMap (.powers a) _ m) =
      (modulesSpecToSheaf.obj N).obj.map (homOfLE inf_le_left).op m :=
  congrArg (fun k => k.hom m) (moduleLocalizationR_unit_lift (.powers a)
    ((modulesSpecToSheaf.obj N).obj.map (homOfLE inf_le_left).op)
    (basicOpenIntersection_scalarUnits N a U))

/--
概要：切断の局所化比較は開集合の制限について自然。
方針：局所化の生成元で二つの線形写像を比較し、元の前層の自然性へ戻す。
規約：対象ごとの写像を同じ前層間の自然変換として束ねる。
使われ方：TT §3、Toën §3.2 の Čech 微分との両立。
-/
def sectionLocalizationComparison :
    (modulesSpecToSheaf.obj N).obj ⋙ moduleLocalizationR (.powers a) ⟶
      (basicOpenIntersectionFunctor a).op ⋙ (modulesSpecToSheaf.obj N).obj where
  app U := sectionLocalizationComparisonAt N a U.unop
  naturality {U V} f := by
    apply moduleLocalizationR_lift_naturality (.powers a)
      ((modulesSpecToSheaf.obj N).obj.map (homOfLE inf_le_left).op)
      ((modulesSpecToSheaf.obj N).obj.map (homOfLE inf_le_left).op)
      ((modulesSpecToSheaf.obj N).obj.map f)
      ((modulesSpecToSheaf.obj N).obj.map ((basicOpenIntersectionFunctor a).map f.unop).op)
      (basicOpenIntersection_scalarUnits N a U.unop)
      (basicOpenIntersection_scalarUnits N a V.unop)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg ((modulesSpecToSheaf.obj N).obj.map) (Subsingleton.elim _ _)

end SerrePositivity.KST.DerivedGeometry
