module
public import SerrePositivity.DifferentialGraded.Module.GradedSplitCokernel
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # u-small余積上の次数付き射と全作用

評価・各次数の余積普遍性を使い、chain条件を課さない分裂を余積に運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
