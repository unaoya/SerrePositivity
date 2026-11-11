module
public import SerrePositivity.KST.SConstruction.EquivalenceDiagrams

/-! # 関手の頂点評価の inner fibration 性
概要：任意の添字の指定頂点での評価は inner fibration。
方針：一点からの内部 Hom の評価を同型とし、頂点の包含による前合成に分解する。
規約：標的のみ quasicategory。使われ方：D(m,w) の評価の全境界持ち上げへの還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：標準一点からの関手の評価は元の単体集合との同型。
方針：定数図式を逆射とし、内部 Hom の自然性と一点の一意性で逆律を示す。
規約：標的の quasicategory 性は不要。使われ方：任意の頂点評価の前合成への分解。 -/
def pointFunctorEvaluationIso (C : SSet.{u}) : (ihom (Δ[0] : SSet.{u})).obj C ≅ C where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  inv := curry (snd (Δ[0] : SSet.{u}) C)
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.functorHom_ext
    intro e α
    apply ConcreteCategory.hom_ext
    intro x
    have hn := ConcreteCategory.congr_hom (F.naturality α (𝟙 d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) d.unop.len)
    have hx : (Δ[0] : SSet.{u}).map α
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) d.unop.len) = x :=
      by
        apply stdSimplex.ext
        intro r
        apply Fin.ext
        omega
    change C.map α (F.app d (𝟙 d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) d.unop.len)) = F.app e α x
    change F.app e ((𝟙 d) ≫ α)
        ((Δ[0] : SSet.{u}).map α
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) d.unop.len)) =
      C.map α (F.app d (𝟙 d)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) d.unop.len)) at hn
    rw [Category.id_comp, hx] at hn
    exact hn.symm
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro c
    change C.map (𝟙 d) c = c
    exact CategoryTheory.Functor.map_id_apply C d c

/-- 概要：任意の頂点での関手評価は一点への制限と一点評価に分解される。
方針：前合成後の評価を頂点の像での評価に直す。
規約：標的の quasicategory 性は不要。使われ方：評価の inner fibration 性。 -/
lemma evaluateFunctorAt_factor {K C : SSet.{u}} (k : K _⦋0⦌) :
    (pre (SSet.yonedaEquiv.symm k)).app C ≫ (pointFunctorEvaluationIso C).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k := by
  change (pre (SSet.yonedaEquiv.symm k)).app C ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  have hk : (SSet.yonedaEquiv.symm k).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = k := by
    have h : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h]
    exact SSet.yonedaEquiv_symm_app_id k
  rw [hk]

/-- 概要：任意の添字の指定頂点での評価は inner fibration。
方針：頂点の包含は単射であり、その前合成と一点評価の同型を合成する。
規約：添字に quasicategory 性は不要。使われ方：全同値図式の評価の相対充填。 -/
instance evaluateFunctorAt_innerFibration {K C : SSet.{u}} [Quasicategory C] (k : K _⦋0⦌) :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) k) := by
  let i : (Δ[0] : SSet.{u}) ⟶ K := SSet.yonedaEquiv.symm k
  let : Mono i := stdSimplex.isTerminalObj₀.mono_from i
  constructor
  rw [← evaluateFunctorAt_factor (C := C) k]
  exact innerFibrations.comp_mem _ _ (mem_innerFibrations ((pre i).app C))
    (MorphismProperty.of_isIso innerFibrations _)

/-- 概要：全同値図式の圏からの任意の頂点評価も inner fibration。
方針：全部分複体の包含と周囲の関手圏の評価を合成する。
規約：標的のみ quasicategory。使われ方：D(m,w) の評価の trivial Kan fibration の還元。 -/
instance equivalenceDiagramEvaluation_innerFibration (K C : SSet.{u}) [Quasicategory C]
    (k : K _⦋0⦌) : InnerFibration (equivalenceDiagramEvaluation K C k) := by
  constructor
  exact innerFibrations.comp_mem _ _
    (mem_innerFibrations (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsEquivalenceDiagramVertex).ι)
    (mem_innerFibrations (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) k))

/-- 概要：D(0,w) の唯一の頂点での評価は元の単体集合との同型。
方針：定数図式を逆とし、一点からの内部 Hom の同型の逆律を包含後で使う。
規約：標的の quasicategory 性は不要。使われ方：object/core 比較の零方向の同定。 -/
def zeroEquivalenceDiagramEvaluationIso (C : SSet.{u}) :
    equivalenceDiagrams (Δ[0] : SSet.{u}) C ≅ C where
  hom := equivalenceDiagramEvaluation Δ[0] C (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  inv := equivalenceDiagramConstant Δ[0] C
  hom_inv_id := by
    have : Mono (equivalenceDiagramι (Δ[0] : SSet.{u}) C) := by
      unfold equivalenceDiagramι
      infer_instance
    apply (cancel_mono (equivalenceDiagramι (Δ[0] : SSet.{u}) C)).1
    rw [Category.assoc, equivalenceDiagramConstant_ι, Category.id_comp]
    change (equivalenceDiagramι (Δ[0] : SSet.{u}) C ≫ (pointFunctorEvaluationIso C).hom) ≫
      (pointFunctorEvaluationIso C).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  inv_hom_id := equivalenceDiagramConstant_evaluation _ _ _

/-- 概要：D(0,w) の評価は同型。
方針：構成した同型の順方向の射を使う。
規約：任意の単体集合。使われ方：零方向の自明ファイブレーション。 -/
instance zeroEquivalenceDiagramEvaluation_isIso (C : SSet.{u}) :
    IsIso (equivalenceDiagramEvaluation (Δ[0] : SSet.{u}) C
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) :=
  inferInstanceAs (IsIso (zeroEquivalenceDiagramEvaluationIso C).hom)

end SerrePositivity.KST.SConstruction
