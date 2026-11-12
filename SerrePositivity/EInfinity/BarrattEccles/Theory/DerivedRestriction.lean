module

public import SerrePositivity.EInfinity.ComplexLimits.StrictHomology
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ScalarRestrictionNerve

/-!
# Barratt–Eccles 実例で使う導来係数制限

## 概要
DAG XIII Construction 2.2.6 の半線形作用を読むため、導来圏の係数制限とホモロジーを比較する。

## 方針
全複体の dg nerve で厳密に係数を制限してから半自由解像を取る。
合成は中間の augmentation を反転して比較する。

## 規約
任意の可換環準同型とすべての余鎖次数を扱う。

## 使われ方
Barratt–Eccles 実例の `restrictD` とその恒等・合成・ホモロジーの欄。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory HomologicalComplex SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open CochainComplex HomComplex

attribute [local instance] HasDerivedCategory.standard
open scoped Simplicial

variable {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]

/-- 全複体の dg nerve での項別係数制限。 -/
def complexRestrictionNerve (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveRestrictScalarsIso f (Complex T)).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (ScalarExtension.restrictionComplexDGFunctor f)

/-- 全複体で係数制限してから半自由解像を取る導来関手。 -/
def barrattEcclesRestrictD (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion ≫ complexRestrictionNerve f ≫ complexSemifreeResolutionInfinity S

/-- 恒等環準同型での項別係数制限は恒等関手。 -/
lemma complexRestrictionNerve_id :
    complexRestrictionNerve (RingHom.id S) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext J a b k hJ ha hb hk
    apply Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    rfl

/-- 項別係数制限は環準同型の合成と厳密に可換。 -/
lemma complexRestrictionNerve_comp (f : S →+* T) (g : T →+* W) :
    complexRestrictionNerve (g.comp f) = complexRestrictionNerve g ≫ complexRestrictionNerve f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext J a b k hJ ha hb hk
    apply Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    rfl

/-- 恒等環準同型の場合は半自由解像の既存の retract 比較。 -/
def barrattEcclesRestrictD_id (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesRestrictD (RingHom.id S)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)) := by
  simpa only [barrattEcclesRestrictD, complexRestrictionNerve_id, Category.id_comp] using
    complexSemifreeResolutionRetractIso S

private lemma restrictCochain_heq (f : S →+* T) {X Y X' Y' : Complex T}
    (hX : X = X') (hY : Y = Y')
    {a : Homogeneous X Y 0} {b : Homogeneous X' Y' 0} (h : HEq a b) :
    HEq (ScalarExtension.restrictCochain f a) (ScalarExtension.restrictCochain f b) := by
  subst X'
  subst Y'
  cases h
  rfl

/-- 係数制限した辺の閉零射は、元の複体射の項別係数制限。 -/
lemma complexRestrictionNerve_edgeChainMap (f : S →+* T)
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T))) x y) :
    (closedToComplex S).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (e.map ((truncation 2).map
      (complexRestrictionNerve f)))) =
      (ScalarExtension.restriction f).map ((closedToComplex T).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) := by
  let e' := e.map ((truncation 2).map (complexRestrictionNerve f))
  apply Cochain.ofHom_injective
  change Cochain.ofHom (complexClosedHomEquiv S _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e')) =
    Cochain.ofHom (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
      (complexClosedHomEquiv T _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)))
  rw [← Cochain.map_ofHom]
  rw [complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
  change (closedHomEquiv S (Complex S) _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e')).val =
    ScalarExtension.restrictCochain f (closedHomEquiv T (Complex T) _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)).val
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle]
  apply eq_of_heq
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq e').trans ((restrictCochain_heq f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e).symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq e)).symm)

/-- 項別係数制限の完全性により、辺の擬同型性を保つ。 -/
lemma complexRestrictionNerve_map_quasiIso (f : S →+* T)
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T))) x y)
    (h : QuasiIso ((closedToComplex T).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))) :
    QuasiIso ((closedToComplex S).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (e.map ((truncation 2).map
      (complexRestrictionNerve f))))) := by
  rw [complexRestrictionNerve_edgeChainMap]
  change QuasiIso (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map _)
  exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _ (hφ := h)

/-- DAG XIII Construction 2.2.6 の係数制限は環射の合成と可換。 -/
def barrattEcclesRestrictD_comp (f : S →+* T) (g : T →+* W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesRestrictD (g.comp f))
      (barrattEcclesRestrictD g ≫ barrattEcclesRestrictD f) := by
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := W) ≫ complexRestrictionNerve g
  let R := complexRestrictionNerve f
  let Q := complexSemifreeResolutionInfinity S
  let H := complexSemifreeResolutionAugmentationHomotopy T
  let K := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H L
  let P := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp K (R ≫ Q)
  have he (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory W) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge P x).toTruncated := by
    let y := atVertex L x
    let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated
    let e' := e.map ((truncation 2).map R)
    have h := complexRestrictionNerve_map_quasiIso f e
      (complexSemifreeResolutionAugmentation_edge_quasiIso T y)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := e'.map ((truncation 2).map Q)) ?_).mpr
    · exact complexSemifreeResolutionInfinity_invertsQuasiIso S e' h
    · change (R ≫ Q).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).edge =
        (R ≫ Q).app (Opposite.op ⦋1⦌) e.edge
      rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge H L x]
      rfl
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy P he).symm
    (by
      change (L ≫ 𝟙 _) ≫ (R ≫ Q) = barrattEcclesRestrictD (g.comp f)
      simp only [barrattEcclesRestrictD, R, Q, L, Category.comp_id,
        complexRestrictionNerve_comp, Category.assoc])
    (by
      change (L ≫ complexSemifreeResolutionInfinity T ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) ≫
        (R ≫ Q) = barrattEcclesRestrictD g ≫ barrattEcclesRestrictD f
      simp only [barrattEcclesRestrictD, R, Q, L, Category.assoc])

/-- 全複体の dg nerve 上の係数制限とホモロジーの自然比較。 -/
def ambientRestrictionHomologyIso (f : S →+* T) (i : ℤ) :
    hoMap (complexRestrictionNerve f) ⋙ ambientCohomology S i ≅
      ambientCohomology T i ⋙ ModuleCat.restrictScalars f := by
  let R := complexRestrictionNerve f
  let M := ModuleCat.restrictScalars f
  let ψ := exactCochainHomologyIso M i
  let a (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T)) _⦋0⦌) := ambientCohomologyVertexIso S i (atVertex R x)
  let b (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T (Complex T)) _⦋0⦌) := M.mapIso (ambientCohomologyVertexIso T i x)
  refine NatIso.ofComponents (SSet.HomotopyCategory.rec
    (fun x => a x ≪≫ ψ.app (x.obj 0) ≪≫ (b x).symm)) ?_
  intro x y h
  induction x using SSet.HomotopyCategory.rec with
  | mk x =>
    induction y using SSet.HomotopyCategory.rec with
    | mk y =>
      obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y h
      let e' := e.map ((truncation 2).map R)
      let k := (closedToComplex T).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)
      change (ambientCohomology S i).map (Truncated.HomotopyCategory.homMk e') ≫
          (a y).hom ≫ (ψ.app (y.obj 0)).hom ≫ (b y).inv =
        ((a x).hom ≫ (ψ.app (x.obj 0)).hom ≫ (b x).inv) ≫
          M.map ((ambientCohomology T i).map (Truncated.HomotopyCategory.homMk e))
      apply (cancel_mono (b y).hom).mp
      have hs := ambientCohomology_map S i e'
      change (ambientCohomology S i).map (Truncated.HomotopyCategory.homMk e') ≫
        (a y).hom = (a x).hom ≫ HomologicalComplex.homologyMap
          ((closedToComplex S).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e')) i at hs
      rw [complexRestrictionNerve_edgeChainMap] at hs
      have ht := congrArg M.map (ambientCohomology_map T i e)
      simp only [Functor.map_comp] at ht
      change M.map ((ambientCohomology T i).map (Truncated.HomotopyCategory.homMk e)) ≫
        (b y).hom = (b x).hom ≫ M.map (HomologicalComplex.homologyMap k i) at ht
      have hn := ψ.hom.naturality k
      change HomologicalComplex.homologyMap ((ScalarExtension.restriction f).map k) i ≫
          (ψ.app (y.obj 0)).hom =
        (ψ.app (x.obj 0)).hom ≫ M.map (HomologicalComplex.homologyMap k i) at hn
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [ht, Iso.inv_hom_id_assoc, ← Category.assoc _ (a y).hom, hs, Category.assoc, hn]

/-- DAG XIII Construction 2.2.6 の半線形作用に用いる可換群の自然比較。 -/
def barrattEcclesRestrictD_homologyIso (f : S →+* T) (i : ℤ) :
    hoMap (barrattEcclesRestrictD f) ⋙ additiveCohomologyOnHo S i ≅
      additiveCohomologyOnHo T i := by
  let I := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := T)
  let R := complexRestrictionNerve f
  let Q := complexSemifreeResolutionInfinity S
  let M := ModuleCat.restrictScalars f
  have h : hoMap (barrattEcclesRestrictD f) ≅ hoMap I ⋙ hoMap R ⋙ hoMap Q := by
    apply eqToIso
    change (hoFunctor.map (I ≫ R ≫ Q)).toFunctor = _
    rw [hoFunctor.map_comp, hoFunctor.map_comp R Q]
    rfl
  have hForget : M ⋙ forget₂ (ModuleCat S) AddCommGrpCat ≅
      forget₂ (ModuleCat T) AddCommGrpCat := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y k
    simpa only [Functor.comp_map, Iso.refl_hom, Category.id_comp, Category.comp_id] using
      ModuleCat.forget₂_map_restrictScalars f k)
  have h' : hoMap (barrattEcclesRestrictD f) ⋙ cohomologyOnHo S i ≅
      cohomologyOnHo T i ⋙ M :=
    Functor.isoWhiskerRight h _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (complexResolutionCohomologyIso S i) ≪≫
        ambientRestrictionHomologyIso f i) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedAmbientCohomologyIso T i).symm M
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h' _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ hForget

end SerrePositivity.EInfinity.ComplexLimits
