module

public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import Mathlib.Algebra.Homology.Localization
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-!
# Module.Disk

## 概要
8 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## GradedCoproduct（旧 SerrePositivity/DifferentialGraded/Module/GradedCoproduct.lean） -/

/-! # u-small余積上の次数付き射と全作用

評価・各次数の余積普遍性を使い、chain条件を課さない分裂を余積に運ぶ。
-/

@[expose] public section GradedCoproduct
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

abbrev moduleDegreeEvaluation (x : D) (n : ℤ) : ModuleCategory A D ⥤ ModuleCat.{u} A :=
  moduleEvaluation A D x ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) n

/-- 評価の各次数で余積包含が余積を与える。 -/
def moduleCoproductDegreeIsColimit (M : J → ModuleCategory A D) (x : D) (n : ℤ) :
    IsColimit (Cofan.mk ((moduleDegreeEvaluation A D x n).obj (∐ M))
      (fun j => (moduleDegreeEvaluation A D x n).map (Sigma.ι M j))) :=
  isColimitOfHasCoproductOfPreservesColimit (moduleDegreeEvaluation A D x n) M

lemma moduleCoproductDegree_hom_ext (M : J → ModuleCategory A D) (x : D) (n : ℤ)
    {P : ModuleCat.{u} A} {f g : (moduleDegreeEvaluation A D x n).obj (∐ M) ⟶ P}
    (h : ∀ j, (moduleDegreeEvaluation A D x n).map (Sigma.ι M j) ≫ f =
      (moduleDegreeEvaluation A D x n).map (Sigma.ι M j) ≫ g) : f = g := by
  apply (moduleCoproductDegreeIsColimit A D M x n).hom_ext
  intro j
  exact h j.as

/-- 任意の次数付き成分族を余積へ拡張する。 -/
def moduleCoproductGradedComponent {M N : J → ModuleCategory A D} (x : D) (n : ℤ)
    (r : ∀ j, ((moduleDegreeEvaluation A D x n).obj (M j)) ⟶
      ((moduleDegreeEvaluation A D x n).obj (N j))) :
    (moduleDegreeEvaluation A D x n).obj (∐ M) ⟶ (moduleDegreeEvaluation A D x n).obj (∐ N) :=
  Cofan.IsColimit.desc (moduleCoproductDegreeIsColimit A D M x n)
    (fun j => r j ≫ (moduleDegreeEvaluation A D x n).map (Sigma.ι N j))

@[reassoc] lemma moduleCoproductGradedComponent_ι {M N : J → ModuleCategory A D} (x : D) (n : ℤ)
    (r : ∀ j, ((moduleDegreeEvaluation A D x n).obj (M j)) ⟶
      ((moduleDegreeEvaluation A D x n).obj (N j))) (j : J) :
    (moduleDegreeEvaluation A D x n).map (Sigma.ι M j) ≫
        moduleCoproductGradedComponent A D x n r =
      r j ≫ (moduleDegreeEvaluation A D x n).map (Sigma.ι N j) :=
by
  unfold moduleCoproductGradedComponent
  simpa only [cofan_mk_inj] using
    (Cofan.IsColimit.fac (moduleCoproductDegreeIsColimit A D M x n)
      (fun t => r t ≫ (moduleDegreeEvaluation A D x n).map (Sigma.ι N t)) j)

lemma moduleCoproductGradedComponent_comp {M N P : J → ModuleCategory A D} (x : D) (n : ℤ)
    (r : ∀ j, (moduleDegreeEvaluation A D x n).obj (M j) ⟶
      (moduleDegreeEvaluation A D x n).obj (N j))
    (s : ∀ j, (moduleDegreeEvaluation A D x n).obj (N j) ⟶
      (moduleDegreeEvaluation A D x n).obj (P j)) :
    moduleCoproductGradedComponent A D x n r ≫ moduleCoproductGradedComponent A D x n s =
      moduleCoproductGradedComponent A D x n (fun j => r j ≫ s j) := by
  apply moduleCoproductDegree_hom_ext A D M x n
  intro j
  rw [← Category.assoc, moduleCoproductGradedComponent_ι, Category.assoc,
    moduleCoproductGradedComponent_ι, moduleCoproductGradedComponent_ι, Category.assoc]

lemma moduleCoproductGradedComponent_id (M : J → ModuleCategory A D) (x : D) (n : ℤ) :
    moduleCoproductGradedComponent A D x n
      (fun j => 𝟙 ((moduleDegreeEvaluation A D x n).obj (M j))) =
      𝟙 _ := by
  apply moduleCoproductDegree_hom_ext A D M x n
  intro j
  rw [moduleCoproductGradedComponent_ι, Category.id_comp]
  exact (Category.comp_id _).symm

lemma moduleCoproductGradedComponent_zero {M N : J → ModuleCategory A D} (x : D) (n : ℤ) :
    moduleCoproductGradedComponent A D x n
      (fun j => (0 : (moduleDegreeEvaluation A D x n).obj (M j) ⟶
        (moduleDegreeEvaluation A D x n).obj (N j))) = 0 := by
  apply moduleCoproductDegree_hom_ext A D M x n
  intro j
  rw [moduleCoproductGradedComponent_ι, zero_comp, comp_zero]

lemma moduleCoproductGradedComponent_add {M N : J → ModuleCategory A D} (x : D) (n : ℤ)
    (r s : ∀ j, (moduleDegreeEvaluation A D x n).obj (M j) ⟶
      (moduleDegreeEvaluation A D x n).obj (N j)) :
    moduleCoproductGradedComponent A D x n (fun j => r j + s j) =
      moduleCoproductGradedComponent A D x n r + moduleCoproductGradedComponent A D x n s := by
  apply moduleCoproductDegree_hom_ext A D M x n
  intro j
  simp only [Preadditive.comp_add, moduleCoproductGradedComponent_ι, Preadditive.add_comp]

lemma moduleCoproductGradedComponent_ofMap {M N : J → ModuleCategory A D}
    (f : ∀ j, M j ⟶ N j) (x : D) (n : ℤ) :
    moduleCoproductGradedComponent A D x n
      (fun j => (moduleDegreeEvaluation A D x n).map (f j)) =
        (moduleDegreeEvaluation A D x n).map (Limits.Sigma.map f) := by
  apply moduleCoproductDegree_hom_ext A D M x n
  intro j
  rw [moduleCoproductGradedComponent_ι, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, Limits.Sigma.ι_map]

/-- 主加群射の全斉次作用に関する成分可換式。 -/
lemma moduleMorphism_actionComponent {M N : ModuleCategory A D} (f : M ⟶ N)
    (x y : D) (p i j : ℤ) (hij : i + p = j) (a : GradedHom A (op x) (op y) p) :
    moduleActionComponent A D M x y p i j hij a ≫ ((moduleEvaluation A D y).map f).f j =
      ((moduleEvaluation A D x).map f).f i ≫ moduleActionComponent A D N x y p i j hij a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact closedFamily_action A (closedTransApp A (moduleClosedHomEquiv A D M N f))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)) (op x) (op y) p i j hij a z

lemma moduleCoproductGradedComponent_naturality {M N : J → ModuleCategory A D}
    (r : ∀ (x : D) (n : ℤ) (t : J), (moduleDegreeEvaluation A D x n).obj (M t) ⟶
      (moduleDegreeEvaluation A D x n).obj (N t))
    (h : ∀ (t : J) (x y : D) (p i j : ℤ) (hij : i + p = j)
      (a : GradedHom A (op x) (op y) p),
      moduleActionComponent A D (M t) x y p i j hij a ≫ r y j t =
        r x i t ≫ moduleActionComponent A D (N t) x y p i j hij a)
    (x y : D) (p i j : ℤ) (hij : i + p = j) (a : GradedHom A (op x) (op y) p) :
    moduleActionComponent A D (∐ M) x y p i j hij a ≫
        moduleCoproductGradedComponent A D y j (r y j) =
      moduleCoproductGradedComponent A D x i (r x i) ≫
        moduleActionComponent A D (∐ N) x y p i j hij a := by
  apply moduleCoproductDegree_hom_ext A D M x i
  intro t
  have hm : moduleActionComponent A D (M t) x y p i j hij a ≫
      (moduleDegreeEvaluation A D y j).map (Sigma.ι M t) =
      (moduleDegreeEvaluation A D x i).map (Sigma.ι M t) ≫
        moduleActionComponent A D (∐ M) x y p i j hij a :=
    moduleMorphism_actionComponent A D (Sigma.ι M t) x y p i j hij a
  have hn : moduleActionComponent A D (N t) x y p i j hij a ≫
      (moduleDegreeEvaluation A D y j).map (Sigma.ι N t) =
      (moduleDegreeEvaluation A D x i).map (Sigma.ι N t) ≫
        moduleActionComponent A D (∐ N) x y p i j hij a :=
    moduleMorphism_actionComponent A D (Sigma.ι N t) x y p i j hij a
  calc
    (moduleDegreeEvaluation A D x i).map (Sigma.ι M t) ≫
        (moduleActionComponent A D (∐ M) x y p i j hij a ≫
          moduleCoproductGradedComponent A D y j (r y j)) =
        (moduleActionComponent A D (M t) x y p i j hij a ≫
          (moduleDegreeEvaluation A D y j).map (Sigma.ι M t)) ≫
          moduleCoproductGradedComponent A D y j (r y j) :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun b =>
        b ≫ moduleCoproductGradedComponent A D y j (r y j)) hm.symm)
    _ = moduleActionComponent A D (M t) x y p i j hij a ≫
        (r y j t ≫ (moduleDegreeEvaluation A D y j).map (Sigma.ι N t)) :=
      (Category.assoc _ _ _).trans (congrArg (fun b =>
        moduleActionComponent A D (M t) x y p i j hij a ≫ b)
          (moduleCoproductGradedComponent_ι A D y j (r y j) t))
    _ = (r x i t ≫ moduleActionComponent A D (N t) x y p i j hij a) ≫
        (moduleDegreeEvaluation A D y j).map (Sigma.ι N t) :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun b =>
        b ≫ (moduleDegreeEvaluation A D y j).map (Sigma.ι N t)) (h t x y p i j hij a))
    _ = r x i t ≫ ((moduleDegreeEvaluation A D x i).map (Sigma.ι N t) ≫
        moduleActionComponent A D (∐ N) x y p i j hij a) :=
      (Category.assoc _ _ _).trans (congrArg (fun b => r x i t ≫ b) hn)
    _ = (moduleDegreeEvaluation A D x i).map (Sigma.ι M t) ≫
        (moduleCoproductGradedComponent A D x i (r x i) ≫
          moduleActionComponent A D (∐ N) x y p i j hij a) :=
      ((Category.assoc _ _ _).symm.trans (congrArg (fun b =>
        b ≫ moduleActionComponent A D (∐ N) x y p i j hij a)
          (moduleCoproductGradedComponent_ι A D x i (r x i) t).symm)).trans
            (Category.assoc _ _ _)

/-- u-small余積は全斉次作用と可換する次数付き分裂を保つ。 -/
def moduleCoproductGradedSplit {M N P : J → ModuleCategory A D}
    (f : ∀ t, M t ⟶ N t) (g : ∀ t, N t ⟶ P t)
    (s : ∀ t, ModuleGradedSplit A D (f t) (g t)) :
    ModuleGradedSplit A D (Limits.Sigma.map f) (Limits.Sigma.map g) where
  retraction x n := moduleCoproductGradedComponent A D x n (fun t => (s t).retraction x n)
  section_ x n := moduleCoproductGradedComponent A D x n (fun t => (s t).section_ x n)
  inclusion_retraction x n := by
    change (moduleDegreeEvaluation A D x n).map (Limits.Sigma.map f) ≫
      moduleCoproductGradedComponent A D x n (fun t => (s t).retraction x n) = 𝟙 _
    rw [← moduleCoproductGradedComponent_ofMap A D f x n, moduleCoproductGradedComponent_comp]
    exact (congrArg (moduleCoproductGradedComponent A D x n)
      (funext (fun t => (s t).inclusion_retraction x n))).trans
        (moduleCoproductGradedComponent_id A D M x n)
  section_projection x n := by
    change moduleCoproductGradedComponent A D x n (fun t => (s t).section_ x n) ≫
      (moduleDegreeEvaluation A D x n).map (Limits.Sigma.map g) = 𝟙 _
    rw [← moduleCoproductGradedComponent_ofMap A D g x n, moduleCoproductGradedComponent_comp]
    exact (congrArg (moduleCoproductGradedComponent A D x n)
      (funext (fun t => (s t).section_projection x n))).trans
        (moduleCoproductGradedComponent_id A D P x n)
  section_retraction x n := by
    rw [moduleCoproductGradedComponent_comp]
    exact (congrArg (moduleCoproductGradedComponent A D x n)
      (funext (fun t => (s t).section_retraction x n))).trans
        (moduleCoproductGradedComponent_zero A D x n)
  inclusion_projection := by
    rw [Limits.Sigma.map_comp_map]
    apply Sigma.hom_ext
    intro t
    rw [Limits.Sigma.ι_map, (s t).inclusion_projection, zero_comp, comp_zero]
  decomposition x n := by
    change moduleCoproductGradedComponent A D x n (fun t => (s t).retraction x n) ≫
        (moduleDegreeEvaluation A D x n).map (Limits.Sigma.map f) +
      (moduleDegreeEvaluation A D x n).map (Limits.Sigma.map g) ≫
        moduleCoproductGradedComponent A D x n (fun t => (s t).section_ x n) = 𝟙 _
    rw [← moduleCoproductGradedComponent_ofMap A D f x n,
      ← moduleCoproductGradedComponent_ofMap A D g x n,
      moduleCoproductGradedComponent_comp, moduleCoproductGradedComponent_comp,
      ← moduleCoproductGradedComponent_add]
    exact (congrArg (moduleCoproductGradedComponent A D x n)
      (funext (fun t => (s t).decomposition x n))).trans
        (moduleCoproductGradedComponent_id A D N x n)
  retraction_naturality x y p i j hij a :=
    moduleCoproductGradedComponent_naturality A D (fun x n t => (s t).retraction x n)
      (fun t => (s t).retraction_naturality) x y p i j hij a
  section_naturality x y p i j hij a :=
    (moduleCoproductGradedComponent_naturality A D (fun x n t => (s t).section_ x n)
      (fun t x y p i j hij a => ((s t).section_naturality x y p i j hij a).symm)
        x y p i j hij a).symm

end SerrePositivity.DifferentialGraded
end

end GradedCoproduct

/-! ## HomotopyQuasiIso（旧 SerrePositivity/DifferentialGraded/Module/HomotopyQuasiIso.lean） -/

/-! # K(D) 上の objectwise quasiIso と閉零圏からの比較 -/

@[expose] public section HomotopyQuasiIso
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D) の射をすべての既存複体ホモトピー圏の評価で判定する。 -/
def moduleHomotopyQuasiIso : MorphismProperty (ModuleHomotopyCategory A D) :=
  fun _ _ f => ∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((moduleHomotopyEvaluation A D x).map f)

/-- K(D) の対象ごとのホモロジー。 -/
def moduleHomotopyHomology (x : D) (i : ℤ) : ModuleHomotopyCategory A D ⥤ ModuleCat A :=
  moduleHomotopyEvaluation A D x ⋙ _root_.HomotopyCategory.homologyFunctor
    (ModuleCat A) (.up ℤ) i

lemma moduleHomotopyQuasiIso_iff {M N : ModuleHomotopyCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D f ↔
      ∀ (x : D) (i : ℤ), IsIso ((moduleHomotopyHomology A D x i).map f) := Iff.rfl

lemma moduleHomotopyQuasiIso_eq_iInf : moduleHomotopyQuasiIso A D =
    ⨅ (x : D) (i : ℤ), (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
      (moduleHomotopyHomology A D x i) := by
  ext M N f
  simp only [moduleHomotopyQuasiIso_iff, MorphismProperty.iInf_iff,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]

instance moduleHomotopyQuasiIsoRespectsIso :
    (moduleHomotopyQuasiIso A D).RespectsIso := by
  rw [moduleHomotopyQuasiIso_eq_iInf]
  infer_instance

instance moduleHomotopyQuasiIsoIsMultiplicative :
    (moduleHomotopyQuasiIso A D).IsMultiplicative where
  id_mem M x i := by
    change IsIso ((moduleHomotopyHomology A D x i).map (𝟙 M))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  comp_mem f g hf hg x i := by
    have : IsIso ((moduleHomotopyHomology A D x i).map f) := hf x i
    have : IsIso ((moduleHomotopyHomology A D x i).map g) := hg x i
    change IsIso ((moduleHomotopyHomology A D x i).map (f ≫ g))
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

instance moduleHomotopyQuasiIsoHasTwoOutOfThree :
    (moduleHomotopyQuasiIso A D).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg x i := by
    let W := (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
      (moduleHomotopyHomology A D x i)
    exact W.of_postcomp (W' := W) f g (hg x i) (hfg x i)
  of_precomp f g hf hfg x i := by
    let W := (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
      (moduleHomotopyHomology A D x i)
    exact W.of_precomp (W' := W) f g (hf x i) (hfg x i)

instance moduleHomotopyQuasiIsoStableUnderRetracts :
    (moduleHomotopyQuasiIso A D).IsStableUnderRetracts where
  of_retract h hg x i :=
    MorphismProperty.of_retract
      (P := (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
        (moduleHomotopyHomology A D x i)) h (hg x i)

/-- K(D) の quasiIso の逆像は、指定した閉零加群の quasiIso と一致する。 -/
lemma moduleHomotopyQuasiIso_map_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map f) ↔
      moduleQuasiIso A D f := by
  change (∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((moduleHomotopyEvaluation A D x).map ((moduleToHomotopy A D).map f))) ↔ _
  change (∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map
      ((moduleEvaluation A D x).map f))) ↔ _
  simp only [_root_.HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff, moduleQuasiIso_iff]

lemma moduleHomotopyQuasiIso_inverseImage :
    (moduleHomotopyQuasiIso A D).inverseImage (moduleToHomotopy A D) =
      moduleQuasiIso A D := by
  ext M N f
  exact moduleHomotopyQuasiIso_map_iff A D f

end SerrePositivity.DifferentialGraded
end

end HomotopyQuasiIso

/-! ## Acyclic（旧 SerrePositivity/DifferentialGraded/Module/Acyclic.lean） -/

/-! # objectwise acyclic な加群と cone による準同型の判定 -/

@[expose] public section Acyclic
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- すべての対象で評価複体が acyclic な加群。 -/
def moduleAcyclic : ObjectProperty (ModuleCategory A D) :=
  fun M => ∀ x : D, ((moduleEvaluation A D x).obj M).Acyclic

lemma moduleAcyclic_iff (M : ModuleCategory A D) :
    moduleAcyclic A D M ↔ ∀ (x : D) (i : ℤ),
      ((moduleEvaluation A D x).obj M).ExactAt i := Iff.rfl

/-- K(D) 上の acyclic 性を、既存の複体ホモトピー圏の評価で判定する。 -/
def moduleHomotopyAcyclic : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun M => ∀ x : D, _root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)
    ((moduleHomotopyEvaluation A D x).obj M)

/-- 商関手は objectwise acyclic 性を保ち、反映する。 -/
lemma moduleHomotopyAcyclic_obj_iff (M : ModuleCategory A D) :
    moduleHomotopyAcyclic A D ((moduleToHomotopy A D).obj M) ↔ moduleAcyclic A D M := by
  change (∀ x : D, _root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)
    ((_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj
      ((moduleEvaluation A D x).obj M))) ↔ _
  simp only [_root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
    moduleAcyclic]

lemma moduleHomotopyAcyclic_iff (M : ModuleHomotopyCategory A D) :
    moduleHomotopyAcyclic A D M ↔ ∀ (x : D) (i : ℤ),
      IsZero ((moduleHomotopyHomology A D x i).obj M) := by
  simp only [moduleHomotopyAcyclic, _root_.HomotopyCategory.mem_subcategoryAcyclic_iff]
  rfl

/-- 加群射の準同型性は、全 dg 作用を持つ標準 cone の objectwise acyclic 性と同値。 -/
lemma moduleQuasiIso_iff_acyclic_cone {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleQuasiIso A D f ↔ moduleAcyclic A D (moduleCone A D f) := by
  change (∀ x : D, QuasiIso ((moduleEvaluation A D x).map f)) ↔
    ∀ x : D, (mappingCone ((moduleEvaluation A D x).map f)).Acyclic
  exact forall_congr' (fun x => complex_quasiIso_iff_acyclic_cone A _)

/-- K(D) の準同型判定にも同じ加群 cone を使用できる。 -/
lemma moduleHomotopyQuasiIso_iff_acyclic_cone {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map f) ↔
      moduleHomotopyAcyclic A D ((moduleToHomotopy A D).obj (moduleCone A D f)) := by
  rw [moduleHomotopyQuasiIso_map_iff, moduleHomotopyAcyclic_obj_iff,
    moduleQuasiIso_iff_acyclic_cone]

end SerrePositivity.DifferentialGraded
end

end Acyclic

/-! ## Cells（旧 SerrePositivity/DifferentialGraded/Module/Cells.lean） -/

/-! # 自由dg加群のsphere/diskとセル境界

freeSphere x nからの射はM(x)の次数nのcycle。
freeDisk x nからの射はM(x)の次数nの任意の要素。
全作用は既存の自由dg加群を再利用する。
-/

@[expose] public section Cells
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev freeSphere (x : D) (n : ℤ) : ModuleCategory A D :=
  (freeAt x).obj (complexSphere A n)

abbrev freeDisk (x : D) (n : ℤ) : ModuleCategory A D :=
  (freeAt x).obj (complexDisk A n)

/-- 生成cellの境界包含。 -/
def freeCellBoundary (x : D) (n : ℤ) : freeSphere A D x (n + 1) ⟶ freeDisk A D x n :=
  (freeAt x).map (complexSphereToDisk A n)

/-- 自由sphereは評価複体のcycleを表現する。 -/
def freeSphereHomEquiv (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeSphere A D x n ⟶ M) ≃ complexCycles A ((moduleEvaluation A D x).obj M) n :=
  (freeHomEquiv A D x (complexSphere A n) M).trans
    (complexSphereHomEquiv A ((moduleEvaluation A D x).obj M) n)

/-- 自由diskは評価複体の任意の斉次生成元を表現する。 -/
def freeDiskHomEquiv (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeDisk A D x n ⟶ M) ≃ ((moduleEvaluation A D x).obj M).X n :=
  (freeHomEquiv A D x (complexDisk A n) M).trans
    (complexDiskHomEquiv A ((moduleEvaluation A D x).obj M) n)

/-- 自由diskの生成元指定は値域に自然。 -/
lemma freeDiskHomEquiv_naturality (x : D) (n : ℤ) {M N : ModuleCategory A D}
    (f : freeDisk A D x n ⟶ M) (g : M ⟶ N) :
    freeDiskHomEquiv A D x n N (f ≫ g) =
      ((moduleEvaluation A D x).map g).f n (freeDiskHomEquiv A D x n M f) := by
  simp only [freeDiskHomEquiv, Equiv.trans_apply, freeHomEquiv_naturality_right]
  exact complexDiskHomEquiv_naturality A n _ _

/-- 自由cellの境界に制限すると、生成元の微分となる。 -/
lemma freeCellBoundary_comp (x : D) (n : ℤ) (M : ModuleCategory A D)
    (f : freeDisk A D x n ⟶ M) :
    (freeSphereHomEquiv A D x (n + 1) M (freeCellBoundary A D x n ≫ f)).val =
      ((moduleEvaluation A D x).obj M).d n (n + 1) (freeDiskHomEquiv A D x n M f) := by
  simp only [freeSphereHomEquiv, freeDiskHomEquiv, freeCellBoundary, Equiv.trans_apply,
    freeHomEquiv_naturality_left]
  exact complexSphereToDisk_comp A n _

/-- 自由diskは任意dg圏でobjectwise acyclic。Hom_Dのflatnessは不要。 -/
lemma freeDisk_acyclic (x : D) (n : ℤ) : moduleAcyclic A D (freeDisk A D x n) := by
  intro y
  exact complexDiskTensor_acyclic A n _

/-- 生成するtrivial cellの入口：零加群から自由diskへの射は準同型。 -/
lemma freeDisk_zeroTo_quasiIso (x : D) (n : ℤ) :
    moduleQuasiIso A D (moduleZeroTo A D (freeDisk A D x n)) := by
  intro y
  rw [quasiIso_iff]
  intro i
  apply (quasiIsoAt_iff_exactAt _ i ?_).2
  · exact freeDisk_acyclic A D x n y i
  · have hz := (moduleEvaluation A D y).map_isZero (moduleZero_isZero A D)
    exact ExactAt.of_isZero ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).map_isZero hz)

end SerrePositivity.DifferentialGraded
end

end Cells

/-! ## CellLifting（旧 SerrePositivity/DifferentialGraded/Module/CellLifting.lean） -/

/-! # 自由diskによる次数ごとの全射性の持ち上げ判定

dg 加群固有の生成元表現を用いる。モデル構造や小対象一般論は定義しない。
-/

@[expose] public section CellLifting
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定した対象・次数の評価で全射となる加群射。 -/
def moduleSurjectiveAt (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) : Prop :=
  Function.Surjective (((moduleEvaluation A D x).map f).f n)

/-- 対象ごと・次数ごとに全射となる加群射のクラス。 -/
def moduleDegreewiseSurjective : MorphismProperty (ModuleCategory A D) :=
  fun _ _ f => ∀ (x : D) (n : ℤ), moduleSurjectiveAt A D x n f

lemma moduleSurjectiveAt_iff_epi (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleSurjectiveAt A D x n f ↔ Epi (((moduleEvaluation A D x).map f).f n) :=
  (ModuleCat.epi_iff_surjective _).symm

/-- 指定の自由diskの零包含に対する右liftは、指定次数の全射性と同値。 -/
lemma freeDisk_lifting_iff_surjective (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    HasLiftingProperty (moduleZeroTo A D (freeDisk A D x n)) f ↔
      moduleSurjectiveAt A D x n f := by
  constructor
  · intro h y
    let g := (freeDiskHomEquiv A D x n N).symm y
    let sq : CommSq (moduleZeroTo A D M) (moduleZeroTo A D (freeDisk A D x n)) f g :=
      ⟨(moduleZero_isZero A D).eq_of_src _ _⟩
    obtain ⟨l⟩ := (h.sq_hasLift sq).exists_lift
    refine ⟨freeDiskHomEquiv A D x n M l.l, ?_⟩
    rw [← freeDiskHomEquiv_naturality, l.fac_right]
    exact (freeDiskHomEquiv A D x n N).apply_symm_apply y
  · intro h
    constructor
    intro a b sq
    obtain ⟨z, hz⟩ := h (freeDiskHomEquiv A D x n N b)
    apply CommSq.HasLift.mk'
    refine { l := (freeDiskHomEquiv A D x n M).symm z
             fac_left := (moduleZero_isZero A D).eq_of_src _ _
             fac_right := ?_ }
    apply (freeDiskHomEquiv A D x n N).injective
    rw [freeDiskHomEquiv_naturality, Equiv.apply_symm_apply]
    exact hz

/-- 自由diskへの零包含の具体的な生成射族J。 -/
def freeDiskInclusions : MorphismProperty (ModuleCategory A D) :=
  MorphismProperty.ofHoms (fun i : D × ℤ => moduleZeroTo A D (freeDisk A D i.1 i.2))

lemma freeDiskInclusions_rlp_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    (freeDiskInclusions A D).rlp f ↔ ∀ (x : D) (n : ℤ),
      HasLiftingProperty (moduleZeroTo A D (freeDisk A D x n)) f := by
  constructor
  · intro h x n
    exact h _ (MorphismProperty.ofHoms.mk (x, n))
  · intro h X Y i hi
    cases hi with
    | mk j => exact h j.1 j.2

/-- Jに対する右持ち上げクラスはちょうどobjectwise degreewise surjective。 -/
lemma freeDiskInclusions_rlp_eq :
    (freeDiskInclusions A D).rlp = moduleDegreewiseSurjective A D := by
  ext M N f
  rw [freeDiskInclusions_rlp_iff]
  change (∀ (x : D) (n : ℤ), HasLiftingProperty (moduleZeroTo A D (freeDisk A D x n)) f) ↔
    ∀ (x : D) (n : ℤ), moduleSurjectiveAt A D x n f
  exact forall_congr' (fun x => forall_congr' (fun n => freeDisk_lifting_iff_surjective A D x n f))

lemma moduleDegreewiseSurjective_iff_epi {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleDegreewiseSurjective A D f ↔ ∀ (x : D) (n : ℤ),
      Epi (((moduleEvaluation A D x).map f).f n) :=
  forall_congr' (fun x => forall_congr' (fun n => moduleSurjectiveAt_iff_epi A D x n f))

instance moduleDegreewiseSurjectiveStableUnderRetracts :
    (moduleDegreewiseSurjective A D).IsStableUnderRetracts := by
  rw [← freeDiskInclusions_rlp_eq]
  infer_instance

instance moduleDegreewiseSurjectiveRespectsIso : (moduleDegreewiseSurjective A D).RespectsIso := by
  rw [← freeDiskInclusions_rlp_eq]
  infer_instance

lemma complexSphereHomEquiv_naturality_val {K L : Complex A} (n : ℤ)
    (a : complexSphere A n ⟶ K) (f : K ⟶ L) :
    (complexSphereHomEquiv A L n (a ≫ f)).val =
      f.f n (complexSphereHomEquiv A K n a).val := by
  change (((HomologicalComplex.singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv) ≫
    (a ≫ f).f n) (1 : A) = _
  rw [HomologicalComplex.comp_f]
  rfl

lemma freeSphereHomEquiv_naturality_val (x : D) (n : ℤ) {M N : ModuleCategory A D}
    (a : freeSphere A D x n ⟶ M) (f : M ⟶ N) :
    (freeSphereHomEquiv A D x n N (a ≫ f)).val =
      ((moduleEvaluation A D x).map f).f n (freeSphereHomEquiv A D x n M a).val := by
  simp only [freeSphereHomEquiv, Equiv.trans_apply, freeHomEquiv_naturality_right]
  exact complexSphereHomEquiv_naturality_val A n _ _

/-- 境界cellのliftを斉次生成元とその微分の方程式として記述する。 -/
def moduleBoundaryLiftAt (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) : Prop :=
  ∀ z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1),
    ∀ y : ((moduleEvaluation A D x).obj N).X n,
      ((moduleEvaluation A D x).map f).f (n + 1) z.val =
        ((moduleEvaluation A D x).obj N).d n (n + 1) y →
      ∃ t : ((moduleEvaluation A D x).obj M).X n,
        ((moduleEvaluation A D x).obj M).d n (n + 1) t = z.val ∧
          ((moduleEvaluation A D x).map f).f n t = y

/-- 全dg自然な境界cellの右liftは、生成元と微分の同時liftに一致する。 -/
lemma freeCellBoundary_lifting_iff (x : D) (n : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    HasLiftingProperty (freeCellBoundary A D x n) f ↔ moduleBoundaryLiftAt A D x n f := by
  constructor
  · intro h z y hz
    let a := (freeSphereHomEquiv A D x (n + 1) M).symm z
    let b := (freeDiskHomEquiv A D x n N).symm y
    have sq : CommSq a (freeCellBoundary A D x n) f b := by
      constructor
      apply (freeSphereHomEquiv A D x (n + 1) N).injective
      apply Subtype.ext
      rw [freeSphereHomEquiv_naturality_val, freeCellBoundary_comp]
      simpa only [a, b, Equiv.apply_symm_apply] using hz
    obtain ⟨l⟩ := (h.sq_hasLift sq).exists_lift
    refine ⟨freeDiskHomEquiv A D x n M l.l, ?_, ?_⟩
    · rw [← freeCellBoundary_comp, l.fac_left]
      exact congrArg Subtype.val ((freeSphereHomEquiv A D x (n + 1) M).apply_symm_apply z)
    · rw [← freeDiskHomEquiv_naturality, l.fac_right]
      exact (freeDiskHomEquiv A D x n N).apply_symm_apply y
  · intro h
    constructor
    intro a b sq
    have hc := congrArg (fun k => (freeSphereHomEquiv A D x (n + 1) N k).val) sq.w
    rw [freeSphereHomEquiv_naturality_val, freeCellBoundary_comp] at hc
    obtain ⟨t, ht, hf⟩ := h (freeSphereHomEquiv A D x (n + 1) M a)
      (freeDiskHomEquiv A D x n N b) hc
    apply CommSq.HasLift.mk'
    refine { l := (freeDiskHomEquiv A D x n M).symm t
             fac_left := ?_
             fac_right := ?_ }
    · apply (freeSphereHomEquiv A D x (n + 1) M).injective
      apply Subtype.ext
      rw [freeCellBoundary_comp, Equiv.apply_symm_apply]
      exact ht
    · apply (freeDiskHomEquiv A D x n N).injective
      rw [freeDiskHomEquiv_naturality, Equiv.apply_symm_apply]
      exact hf

/-- 全次数で境界cellをliftできれば、まずcycleをliftし、その後任意の生成元をliftできる。 -/
lemma moduleSurjectiveAt_of_boundary_lifting (x : D) {M N : ModuleCategory A D} (f : M ⟶ N)
    (h : ∀ n : ℤ, moduleBoundaryLiftAt A D x n f) (n : ℤ) : moduleSurjectiveAt A D x n f := by
  intro y
  let y₁ := ((moduleEvaluation A D x).obj N).d n (n + 1) y
  have hy₁ : ((moduleEvaluation A D x).obj N).d (n + 1) (n + 1 + 1) y₁ = 0 := by
    have hd := ((moduleEvaluation A D x).obj N).d_comp_d n (n + 1) (n + 1 + 1)
    have he := congrArg (fun k => k y) hd
    exact he
  have hc : ((moduleEvaluation A D x).map f).f (n + 1 + 1)
      (0 : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1 + 1)).val =
      ((moduleEvaluation A D x).obj N).d (n + 1) (n + 1 + 1) y₁ := by
    rw [hy₁]
    exact map_zero _
  obtain ⟨z, hz, hf⟩ := h (n + 1) 0 y₁ hc
  let zc : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1) := ⟨z, hz⟩
  obtain ⟨t, _, ht⟩ := h n zc y hf
  exact ⟨t, ht⟩

/-- 自由sphere→diskの生成射族I。 -/
def freeCellBoundaries : MorphismProperty (ModuleCategory A D) :=
  MorphismProperty.ofHoms (fun i : D × ℤ => freeCellBoundary A D i.1 i.2)

lemma freeCellBoundaries_rlp_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    (freeCellBoundaries A D).rlp f ↔ ∀ (x : D) (n : ℤ), moduleBoundaryLiftAt A D x n f := by
  constructor
  · intro h x n
    exact (freeCellBoundary_lifting_iff A D x n f).1 (h _ (MorphismProperty.ofHoms.mk (x, n)))
  · intro h X Y i hi
    cases hi with
    | mk j => exact (freeCellBoundary_lifting_iff A D j.1 j.2 f).2 (h j.1 j.2)

/-- Iに対する右liftは各評価・次数でepiとなることを含意する。 -/
lemma freeCellBoundaries_rlp_degreewiseSurjective :
    (freeCellBoundaries A D).rlp ≤ moduleDegreewiseSurjective A D := by
  intro M N f hf x n
  exact moduleSurjectiveAt_of_boundary_lifting A D x f
    ((freeCellBoundaries_rlp_iff A D f).1 hf x) n

/-- 全評価で境界cellをliftできればobjectwise準同型となる。 -/
lemma moduleQuasiIso_of_boundary_lifting {M N : ModuleCategory A D} (f : M ⟶ N)
    (h : ∀ (x : D) (n : ℤ), moduleBoundaryLiftAt A D x n f) : moduleQuasiIso A D f := by
  intro x
  exact complex_quasiIso_of_boundary_lifting A ((moduleEvaluation A D x).map f) (h x)

lemma moduleBoundaryLiftAt_of_surjective_quasiIso {M N : ModuleCategory A D} (f : M ⟶ N)
    (hs : moduleDegreewiseSurjective A D f) (hq : moduleQuasiIso A D f) (x : D) (n : ℤ) :
    moduleBoundaryLiftAt A D x n f :=
  complex_boundary_lifting_of_surjective_quasiIso A ((moduleEvaluation A D x).map f)
    (hs x) (hq x) n

/-- Iに対する右liftはちょうど次数ごと全射なobjectwise準同型。 -/
lemma freeCellBoundaries_rlp_eq : (freeCellBoundaries A D).rlp =
    moduleDegreewiseSurjective A D ⊓ moduleQuasiIso A D := by
  ext M N f
  constructor
  · intro hf
    exact ⟨freeCellBoundaries_rlp_degreewiseSurjective A D f hf,
      moduleQuasiIso_of_boundary_lifting A D f ((freeCellBoundaries_rlp_iff A D f).1 hf)⟩
  · rintro ⟨hs, hq⟩
    apply (freeCellBoundaries_rlp_iff A D f).2
    exact moduleBoundaryLiftAt_of_surjective_quasiIso A D f hs hq

end SerrePositivity.DifferentialGraded
end

end CellLifting

/-! ## DiskCover（旧 SerrePositivity/DifferentialGraded/Module/DiskCover.lean） -/

/-! # 自由diskの余積による任意dg加群の次数ごと全射な被覆

各対象・整数次数・斉次要素について自由diskを一つ取り、その生成元を指定要素へ送る。
添字はu-smallで、全作用と余積は主加群圏の既存構成を再利用する。
-/

@[expose] public section DiskCover
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 被覆の生成元：対象・次数・その評価での斉次要素。 -/
def ModuleDiskCoverIndex (M : ModuleCategory A D) :=
  Σ x : D, Σ n : ℤ, ((moduleEvaluation A D x).obj M).X n

instance moduleDiskCoverIndexSmall (M : ModuleCategory A D) :
    Small.{u} (ModuleDiskCoverIndex A D M) := by
  unfold ModuleDiskCoverIndex
  infer_instance

def moduleDiskCoverFamily (M : ModuleCategory A D) :
    ModuleDiskCoverIndex A D M → ModuleCategory A D :=
  fun j => freeDisk A D j.1 j.2.1

/-- 自由diskのu-small余積。 -/
def moduleDiskCover (M : ModuleCategory A D) : ModuleCategory A D := ∐ moduleDiskCoverFamily A D M

def moduleDiskCoverι (M : ModuleCategory A D) (j : ModuleDiskCoverIndex A D M) :
    moduleDiskCoverFamily A D M j ⟶ moduleDiskCover A D M :=
  Sigma.ι (moduleDiskCoverFamily A D M) j

/-- 全斉次生成元を指定された像へ送る被覆射。 -/
def moduleDiskCoverπ (M : ModuleCategory A D) : moduleDiskCover A D M ⟶ M :=
  Sigma.desc (fun j : ModuleDiskCoverIndex A D M =>
    (freeDiskHomEquiv A D j.1 j.2.1 M).symm j.2.2)

@[reassoc]
lemma moduleDiskCoverι_π (M : ModuleCategory A D) (j : ModuleDiskCoverIndex A D M) :
    moduleDiskCoverι A D M j ≫ moduleDiskCoverπ A D M =
      (freeDiskHomEquiv A D j.1 j.2.1 M).symm j.2.2 :=
  Sigma.ι_comp_desc _ _

/-- 被覆射は全対象・全整数次数で全射。 -/
lemma moduleDiskCoverπ_degreewiseSurjective (M : ModuleCategory A D) :
    moduleDegreewiseSurjective A D (moduleDiskCoverπ A D M) := by
  intro x n y
  let j : ModuleDiskCoverIndex A D M := ⟨x, n, y⟩
  refine ⟨freeDiskHomEquiv A D x n (moduleDiskCover A D M) (moduleDiskCoverι A D M j), ?_⟩
  have h := congrArg (freeDiskHomEquiv A D x n M) (moduleDiskCoverι_π A D M j)
  rw [freeDiskHomEquiv_naturality] at h
  exact h.trans ((freeDiskHomEquiv A D x n M).apply_symm_apply y)

end SerrePositivity.DifferentialGraded
end

end DiskCover

/-! ## DiskFiltration（旧 SerrePositivity/DifferentialGraded/Module/DiskFiltration.lean） -/

/-! # 自由diskの自由sphereによる二段filtration -/

@[expose] public section DiskFiltration
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def freeDiskToSphere (x : D) (n : ℤ) : freeDisk A D x n ⟶ freeSphere A D x n :=
  (freeAt x).map (complexDiskToSphere A n)

@[simp] lemma freeDiskToSphere_eval (x y : D) (n : ℤ) :
    (moduleEvaluation A D y).map (freeDiskToSphere A D x n) =
      complexDiskToSphere A n ▷ (y ⟶[Complex A] x) :=
  tensorModuleMap_eval _ _ _

@[simp] lemma freeCellBoundary_eval (x y : D) (n : ℤ) :
    (moduleEvaluation A D y).map (freeCellBoundary A D x n) =
      complexSphereToDisk A n ▷ (y ⟶[Complex A] x) :=
  tensorModuleMap_eval _ _ _

lemma freeCellBoundary_toSphere (x : D) (n : ℤ) :
    freeCellBoundary A D x n ≫ freeDiskToSphere A D x n = 0 := by
  apply moduleMorphism_ext
  intro y
  rw [CategoryTheory.Functor.map_comp, freeCellBoundary_eval, freeDiskToSphere_eval,
    CategoryTheory.Functor.map_zero, ← comp_whiskerRight, complexSphereToDiskToSphere,
    MonoidalPreadditive.zero_whiskerRight]

/-- 自由diskの二段filtrationは全斉次作用に関して分裂する。 -/
def freeDiskGradedSplit (x : D) (n : ℤ) :
    ModuleGradedSplit A D (freeCellBoundary A D x n) (freeDiskToSphere A D x n) where
  retraction y k := tensorGradedZeroComponent (complexDiskGradedRetraction A n)
    (y ⟶[Complex A] x) k
  section_ y k := tensorGradedZeroComponent (complexDiskGradedSection A n)
    (y ⟶[Complex A] x) k
  inclusion_retraction y k := by
    rw [freeCellBoundary_eval]
    change (complexSphereToDisk A n ▷ (y ⟶[Complex A] x)).f k ≫
      tensorGradedZeroComponent (complexDiskGradedRetraction A n) (y ⟶[Complex A] x) k = 𝟙 _
    rw [← tensorGradedZeroComponent_ofHom, tensorGradedZeroComponent_comp,
      complexDiskGraded_inclusion_retraction_cochain, tensorGradedZeroComponent_id]
  section_projection y k := by
    rw [freeDiskToSphere_eval]
    change tensorGradedZeroComponent (complexDiskGradedSection A n) (y ⟶[Complex A] x) k ≫
      (complexDiskToSphere A n ▷ (y ⟶[Complex A] x)).f k = 𝟙 _
    rw [← tensorGradedZeroComponent_ofHom, tensorGradedZeroComponent_comp,
      complexDiskGraded_section_projection_cochain, tensorGradedZeroComponent_id]
  section_retraction y k := by
    rw [tensorGradedZeroComponent_comp, complexDiskGraded_section_retraction_cochain,
      tensorGradedZeroComponent_zero]
  inclusion_projection := freeCellBoundary_toSphere A D x n
  decomposition y k := by
    rw [freeCellBoundary_eval, freeDiskToSphere_eval]
    change tensorGradedZeroComponent (complexDiskGradedRetraction A n) (y ⟶[Complex A] x) k ≫
        (complexSphereToDisk A n ▷ (y ⟶[Complex A] x)).f k +
      (complexDiskToSphere A n ▷ (y ⟶[Complex A] x)).f k ≫
        tensorGradedZeroComponent (complexDiskGradedSection A n) (y ⟶[Complex A] x) k = 𝟙 _
    rw [← tensorGradedZeroComponent_ofHom, ← tensorGradedZeroComponent_ofHom,
      tensorGradedZeroComponent_comp, tensorGradedZeroComponent_comp,
      ← tensorGradedZeroComponent_add, complexDiskGraded_decomposition_cochain,
      tensorGradedZeroComponent_id]
  retraction_naturality y z p i j hij a :=
    tensorGradedZeroComponent_naturality _ p i j hij _
  section_naturality y z p i j hij a :=
    (tensorGradedZeroComponent_naturality _ p i j hij _).symm

lemma freeCellBoundary_mono (x : D) (n : ℤ) : Mono (freeCellBoundary A D x n) :=
  (freeDiskGradedSplit A D x n).mono

lemma freeDiskToSphere_epi (x : D) (n : ℤ) : Epi (freeDiskToSphere A D x n) :=
  (freeDiskGradedSplit A D x n).epi

/-- 自由diskの商は同じ対象xで生成する次数nの自由sphere。 -/
def freeDiskSphereCokernel (x : D) (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (freeDiskToSphere A D x n) (freeCellBoundary_toSphere A D x n)) :=
  moduleGradedSplitCokernel A D (freeDiskGradedSplit A D x n)

end SerrePositivity.DifferentialGraded
end

end DiskFiltration

/-! ## DiskCoverFiltration（旧 SerrePositivity/DifferentialGraded/Module/DiskCoverFiltration.lean） -/

/-! # 初期自由disk被覆全体の二段sphere filtration -/

@[expose] public section DiskCoverFiltration
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDiskCoverUpperFamily (M : ModuleCategory A D) :
    ModuleDiskCoverIndex A D M → ModuleCategory A D :=
  fun t => freeSphere A D t.1 (t.2.1 + 1)

def moduleDiskCoverLowerFamily (M : ModuleCategory A D) :
    ModuleDiskCoverIndex A D M → ModuleCategory A D :=
  fun t => freeSphere A D t.1 t.2.1

/-- 初期被覆の部分加群は上次数自由sphereの余積。 -/
def moduleDiskCoverBoundary (M : ModuleCategory A D) :
    (∐ moduleDiskCoverUpperFamily A D M) ⟶ moduleDiskCover A D M :=
  Limits.Sigma.map (fun t : ModuleDiskCoverIndex A D M => freeCellBoundary A D t.1 t.2.1)

/-- 初期被覆の商は下次数自由sphereの余積。 -/
def moduleDiskCoverQuotient (M : ModuleCategory A D) :
    moduleDiskCover A D M ⟶ (∐ moduleDiskCoverLowerFamily A D M) :=
  Limits.Sigma.map (fun t : ModuleDiskCoverIndex A D M => freeDiskToSphere A D t.1 t.2.1)

def moduleDiskCoverGradedSplit (M : ModuleCategory A D) :
    ModuleGradedSplit A D (moduleDiskCoverBoundary A D M) (moduleDiskCoverQuotient A D M) :=
  moduleCoproductGradedSplit A D
    (fun t : ModuleDiskCoverIndex A D M => freeCellBoundary A D t.1 t.2.1)
    (fun t : ModuleDiskCoverIndex A D M => freeDiskToSphere A D t.1 t.2.1)
    (fun t => freeDiskGradedSplit A D t.1 t.2.1)

lemma moduleDiskCoverBoundary_mono (M : ModuleCategory A D) :
    Mono (moduleDiskCoverBoundary A D M) := (moduleDiskCoverGradedSplit A D M).mono

lemma moduleDiskCoverQuotient_epi (M : ModuleCategory A D) :
    Epi (moduleDiskCoverQuotient A D M) := (moduleDiskCoverGradedSplit A D M).epi

def moduleDiskCoverSphereCokernel (M : ModuleCategory A D) :
    IsColimit (CokernelCofork.ofπ (moduleDiskCoverQuotient A D M)
      (moduleDiskCoverGradedSplit A D M).inclusion_projection) :=
  moduleGradedSplitCokernel A D (moduleDiskCoverGradedSplit A D M)

end SerrePositivity.DifferentialGraded
end

end DiskCoverFiltration
