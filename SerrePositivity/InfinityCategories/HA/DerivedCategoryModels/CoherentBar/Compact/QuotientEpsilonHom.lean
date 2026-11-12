module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
概要：固定 ε と整合する null 保存関手間の Hom 部分複体を構成する。
方針：元の変換と商上の変換の全対象成分を一致させる pullback を使う。
規約：元 Hom への射は単射であり、商上の変換を追加選択データとして残さない。
使われ方：D-S 工程2の NullPreservingFunctorsε と商関手変数の豊穣作用。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (D : Type w) [DGCategory R D] (S : Set C) (T : Set D)

/-- ε 整合 Hom を持つ圏の対象。対象自体は元の null 保存 dg 関手。 -/
structure NullPreservingFunctorsε where
  val : DGFunctor R C D
  property : ∀ x ∈ S, val.obj x ∈ T

variable [Small.{u} C] [Small.{u} D]
local instance : HasProductsOfShape C (ModuleCat.{u} R) := ModuleCat.hasLimitsOfShape

/-- 対象作用は、既存の同じ固定 ε を持つ正本商関手。 -/
def quotientEpsilonObject (F : NullPreservingFunctorsε R C D S T) :
    DGFunctor R (DGQuotient.QuotientObject C S) (DGQuotient.QuotientObject D T) :=
  DGQuotient.quotientDGFunctor R C D F.val S T F.property

/-- 比較先は、元の各対象での商内の Hom の全積。 -/
abbrev quotientEpsilonComponentFamily (F G : NullPreservingFunctorsε R C D S T) :
    C → Complex R :=
  fun x => homObject R (DGQuotient.QuotientObject D T)
    ⟨F.val.obj x⟩ ⟨G.val.obj x⟩

/-- 元 Hom の全対象成分を、同じ標的商の Hom に写す。 -/
def quotientEpsilonOriginalComponents (F G : NullPreservingFunctorsε R C D S T) :
    dgFunctorHom R C D F.val G.val ⟶ ∏ᶜ quotientEpsilonComponentFamily R C D S T F G :=
  Pi.lift (fun x => dgFunctorHomπ R C D F.val G.val x ≫
    (DGQuotient.inclusion R D T).map (F.val.obj x) (G.val.obj x))

/-- 商上の変換の全対象成分を、元の同じ対象ラベルで読む。 -/
def quotientEpsilonExtendedComponents (F G : NullPreservingFunctorsε R C D S T) :
    dgFunctorHom R _ _ (quotientEpsilonObject R C D S T F)
        (quotientEpsilonObject R C D S T G) ⟶
      ∏ᶜ quotientEpsilonComponentFamily R C D S T F G :=
  Pi.lift (fun x => dgFunctorHomπ R (DGQuotient.QuotientObject C S)
    (DGQuotient.QuotientObject D T) (quotientEpsilonObject R C D S T F)
      (quotientEpsilonObject R C D S T G) ⟨x⟩)

@[reassoc (attr := simp)]
lemma quotientEpsilonOriginalComponents_π (F G : NullPreservingFunctorsε R C D S T)
    (x : C) :
    quotientEpsilonOriginalComponents R C D S T F G ≫
        Pi.π (quotientEpsilonComponentFamily R C D S T F G) x =
      dgFunctorHomπ R C D F.val G.val x ≫
        (DGQuotient.inclusion R D T).map (F.val.obj x) (G.val.obj x) :=
  by simp only [quotientEpsilonOriginalComponents, Pi.lift_comp_π]

@[reassoc (attr := simp)]
lemma quotientEpsilonExtendedComponents_π (F G : NullPreservingFunctorsε R C D S T)
    (x : C) :
    quotientEpsilonExtendedComponents R C D S T F G ≫
        Pi.π (quotientEpsilonComponentFamily R C D S T F G) x =
      dgFunctorHomπ R _ _ _ _ (⟨x⟩ : DGQuotient.QuotientObject C S) :=
  by simp only [quotientEpsilonExtendedComponents, Pi.lift_comp_π]

/-- 商は対象を変えないので、全対象成分を読む射は単射である。 -/
instance quotientEpsilonExtendedComponents_mono
    (F G : NullPreservingFunctorsε R C D S T) :
    Mono (quotientEpsilonExtendedComponents R C D S T F G) := by
  constructor
  intro X f g h
  apply dgFunctorHom_ext
  intro x
  rcases x with ⟨x⟩
  have hx := congrArg
    (fun z => z ≫ Pi.π (quotientEpsilonComponentFamily R C D S T F G) x) h
  simpa only [Category.assoc, quotientEpsilonExtendedComponents_π] using hx

/-- 固定 ε と整合する Hom 部分複体の pullback 表示。 -/
abbrev quotientEpsilonHom (F G : NullPreservingFunctorsε R C D S T) : Complex R :=
  pullback (quotientEpsilonOriginalComponents R C D S T F G)
    (quotientEpsilonExtendedComponents R C D S T F G)

/-- 元の全次数 Hom end への部分複体包含。 -/
def quotientEpsilonHomι (F G : NullPreservingFunctorsε R C D S T) :
    quotientEpsilonHom R C D S T F G ⟶ dgFunctorHom R C D F.val G.val :=
  pullback.fst _ _

/-- 同じ成分を持つ商上の変換への、選択を伴わない実延長。 -/
def quotientEpsilonHomExtension (F G : NullPreservingFunctorsε R C D S T) :
    quotientEpsilonHom R C D S T F G ⟶
      dgFunctorHom R _ _ (quotientEpsilonObject R C D S T F)
        (quotientEpsilonObject R C D S T G) :=
  pullback.snd _ _

instance quotientEpsilonHomι_mono (F G : NullPreservingFunctorsε R C D S T) :
    Mono (quotientEpsilonHomι R C D S T F G) := by
  dsimp only [quotientEpsilonHomι]
  infer_instance

/-- 延長の各対象成分は、元の同じ変換成分の商包含像に厳密に一致する。 -/
@[reassoc]
lemma quotientEpsilonHomExtension_π (F G : NullPreservingFunctorsε R C D S T) (x : C) :
    quotientEpsilonHomExtension R C D S T F G ≫ dgFunctorHomπ R _ _ _ _ ⟨x⟩ =
      quotientEpsilonHomι R C D S T F G ≫ dgFunctorHomπ R C D F.val G.val x ≫
        (DGQuotient.inclusion R D T).map (F.val.obj x) (G.val.obj x) := by
  have h := congrArg
    (fun z => z ≫ Pi.π (quotientEpsilonComponentFamily R C D S T F G) x)
    (pullback.condition (f := quotientEpsilonOriginalComponents R C D S T F G)
      (g := quotientEpsilonExtendedComponents R C D S T F G))
  simpa only [Category.assoc, quotientEpsilonOriginalComponents_π,
    quotientEpsilonExtendedComponents_π, quotientEpsilonHomExtension,
    quotientEpsilonHomι] using h.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
