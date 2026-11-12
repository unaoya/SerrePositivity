module
public import SerrePositivity.KST.SConstruction.TrivialFibrationPrism
public import SerrePositivity.KST.SConstruction.ArrowSourcePrism
public import SerrePositivity.KST.SConstruction.CofiberEvaluations

/-! # McCarthy の λ から元の cofiber 図式 ν への変換
概要：標準恒等 cofiber から元の cofiber への自然変換を、入力の辺の普遍 prism から持ち上げる。
方針：cofiber 射影の自明ファイブレーションで両端を指定する。
規約：subobject の成分を厳密に一定に保つ。使われ方：McCarthy の押し出し span の左辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：標準恒等 cofiber の入力は恒等な辺の関手。
方針：正方形の下辺では零射の自然変換の始点を取る。
規約：両端だけでなく辺全体の厳密な等号。使われ方：λ→ν の基底の端点。 -/
lemma zeroCofiberFunctor_identityProjection {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) : zeroCofiberFunctor z false ≫ cofiberProjection C =
      curry (snd (Δ[1] : SSet.{u}) C) := by
  rw [cofiberProjection, ← Category.assoc, zeroCofiberFunctor_ι]
  apply uncurry_injective
  rw [uncurry_pre_app, zeroCofiberSquare, uncurry_curry, uncurry_curry]
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ▷ C) ≫ (identityPushoutShape false ▷ C) =
      snd (Δ[1] : SSet.{u}) C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 C := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [← Category.assoc, h, Category.assoc, zeroNaturalTransformation_zero]
  simp

private lemma lambdaNu_start {C : SSet.{u}} [Quasicategory C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (cofiberDiagrams C) ≫
      ((Δ[1] ◁ cofiberProjection C) ≫ arrowSourcePrism C) =
      (cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        zeroCofiberFunctor z false) ≫ cofiberProjection C := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, arrowSourcePrism_zero]
  simp only [Category.assoc]
  rw [zeroCofiberFunctor_identityProjection]

private lemma lambdaNu_end (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (cofiberDiagrams C) ≫
      ((Δ[1] ◁ cofiberProjection C) ≫ arrowSourcePrism C) = (𝟙 _) ≫ cofiberProjection C := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, arrowSourcePrism_one,
    Category.comp_id, Category.id_comp]

/-- 概要：全 cofiber 図式に自然な標準恒等 cofiber から元の図式への prism。
方針：入力の辺の普遍 prism を両端指定で持ち上げる。
規約：一つの大域的な選択を全ての図式に使う。使われ方：λ→ν の coherent な左辺。 -/
def cofiberLambdaNu {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    (Δ[1] : SSet.{u}) ⊗ cofiberDiagrams C ⟶ cofiberDiagrams C :=
  liftPrismOfTrivialKanFibration (cofiberProjection C)
    (cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
      zeroCofiberFunctor z false) (𝟙 _)
    ((Δ[1] ◁ cofiberProjection C) ≫ arrowSourcePrism C) (by exact lambdaNu_start z)
      (by exact lambdaNu_end C)

/-- 概要：左辺の普遍 prism の始点は subobject の標準恒等 cofiber。
方針：両端指定の持ち上げの始点。
規約：射の厳密な等号。使われ方：span の共通始点。 -/
lemma cofiberLambdaNu_zero {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (cofiberDiagrams C) ≫ cofiberLambdaNu z =
      cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        zeroCofiberFunctor z false := liftPrismOfTrivialKanFibration_zero _ _ _ _ _ _

/-- 概要：左辺の普遍 prism の終点は元の cofiber 図式。
方針：両端指定の持ち上げの終点。
規約：射の厳密な等号。使われ方：ν の頂点。 -/
lemma cofiberLambdaNu_one {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (cofiberDiagrams C) ≫ cofiberLambdaNu z = 𝟙 _ :=
  liftPrismOfTrivialKanFibration_one _ _ _ _ _ _

/-- 概要：左辺の普遍 prism は入力の辺の普遍変換を厳密に覆う。
方針：自明ファイブレーションによる持ち上げの射影の式。
規約：全パラメーターでの等号。使われ方：subobject の恒等成分の証明。 -/
lemma cofiberLambdaNu_projection {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) : cofiberLambdaNu z ≫ cofiberProjection C =
      (Δ[1] ◁ cofiberProjection C) ≫ arrowSourcePrism C :=
  liftPrismOfTrivialKanFibration_projection _ _ _ _ _ _

/-- 概要：左辺の普遍 prism の subobject は時刻によらず一定。
方針：入力の辺での厳密な射影の式と始点の成分の固定を使う。
規約：任意の cofiber 図式に同時に成立。使われ方：押し出し ρ の subobject の厳密な回収。 -/
lemma cofiberLambdaNu_source {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) :
    cofiberLambdaNu z ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      snd (Δ[1] : SSet.{u}) (cofiberDiagrams C) ≫ cofiberProjection C ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [← Category.assoc, cofiberLambdaNu_projection, Category.assoc, arrowSourcePrism_source]
  rfl

/-- 概要：任意の Ar 図式への λ→ν の左辺の prism。
方針：全 cofiber 図式上の普遍 prism を図式で引き戻す。
規約：対象ごとの変換の選択をしない。使われ方：McCarthy の span の図式。 -/
def mcCarthyLambdaNu {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (E : arNerve n ⟶ cofiberDiagrams C) :
    (Δ[1] : SSet.{u}) ⊗ arNerve n ⟶ cofiberDiagrams C :=
  (Δ[1] ◁ E) ≫ cofiberLambdaNu z

/-- 概要：Ar の図式への左辺の prism は全ての添字の前合成と両立する。
方針：パラメーターの引き戻しの合成則。
規約：面・退化に共通の厳密な等号。使われ方：ρ の単体的自然性。 -/
lemma mcCarthyLambdaNu_pre {l n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (E : arNerve n ⟶ cofiberDiagrams C)
    (σ : Fin (l + 1) →o Fin (n + 1)) :
    (Δ[1] ◁ arNerveMap σ) ≫ mcCarthyLambdaNu z E =
      mcCarthyLambdaNu z (arNerveMap σ ≫ E) := by
  rw [mcCarthyLambdaNu, ← Category.assoc, ← whiskerLeft_comp]
  rfl

/-- 概要：Ar の図式への左辺の prism の始点は元の subobject の標準恒等 cofiber。
方針：prism の端点の自然性と普遍 prism の始点の式。
規約：射の厳密な等号。使われ方：λ と共通始点の照合。 -/
lemma mcCarthyLambdaNu_zero {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (E : arNerve n ⟶ cofiberDiagrams C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (arNerve n) ≫ mcCarthyLambdaNu z E =
      E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        zeroCofiberFunctor z false := by
  rw [mcCarthyLambdaNu, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    cofiberLambdaNu_zero]

/-- 概要：Ar の図式への左辺の prism の終点は元の図式。
方針：prism の端点の自然性と普遍 prism の終点の式。
規約：射の厳密な等号。使われ方：ν の頂点。 -/
lemma mcCarthyLambdaNu_one {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (E : arNerve n ⟶ cofiberDiagrams C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (arNerve n) ≫ mcCarthyLambdaNu z E = E := by
  rw [mcCarthyLambdaNu, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    cofiberLambdaNu_one, Category.comp_id]

/-- 概要：Ar の図式への左辺の prism の subobject は元の subobject で一定。
方針：普遍 prism の始点成分の固定の式を図式で引き戻す。
規約：全単体での等号。使われ方：ρ の subobject を μ の図式として厳密に回収する。 -/
lemma mcCarthyLambdaNu_source {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C) (E : arNerve n ⟶ cofiberDiagrams C) :
    mcCarthyLambdaNu z E ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      snd (Δ[1] : SSet.{u}) (arNerve n) ≫ E ≫ cofiberProjection C ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [mcCarthyLambdaNu, Category.assoc, cofiberLambdaNu_source]
  rfl

end SerrePositivity.KST.SConstruction
