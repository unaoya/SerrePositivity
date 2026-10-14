module
public import SerrePositivity.DifferentialGraded.Module.ConeMaps
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # 可換 square の cone 射と関手性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 全次数自然な可換 square の objectwise cone 射も全次数自然。 -/
lemma coneFamilyMap_naturality {M N M' N' : RightModule A D}
    (f : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x) (g : ∀ x : Dᵒᵖ, M'.obj x ⟶ N'.obj x)
    (hf : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (f y) =
      N.map x y ≫ homPrecompose (f x) (N.obj y))
    (hg : ∀ x y, M'.map x y ≫ homPostcompose (M'.obj x) (g y) =
      N'.map x y ≫ homPrecompose (g x) (N'.obj y))
    (u : ∀ x : Dᵒᵖ, M.obj x ⟶ M'.obj x) (v : ∀ x : Dᵒᵖ, N.obj x ⟶ N'.obj x)
    (hu : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (u y) =
      M'.map x y ≫ homPrecompose (u x) (M'.obj y))
    (hv : ∀ x y, N.map x y ≫ homPostcompose (N.obj x) (v y) =
      N'.map x y ≫ homPrecompose (v x) (N'.obj y))
    (comm : ∀ x, f x ≫ v x = u x ≫ g x) (x y : Dᵒᵖ) :
    (coneModule M N f hf).map x y ≫ homPostcompose (mappingCone (f x))
      (mappingCone.map (f y) (g y) (u y) (v y) (comm y)) =
    (coneModule M' N' g hg).map x y ≫ homPrecompose
      (mappingCone.map (f x) (g x) (u x) (v x) (comm x)) (mappingCone (g y)) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (coneMapCochain (f x) (f y) ((M.map x y).f p t) ((N.map x y).f p t)).comp
      (Cochain.ofHom (mappingCone.map (f y) (g y) (u y) (v y) (comm y))) (add_zero p) =
    (Cochain.ofHom (mappingCone.map (f x) (g x) (u x) (v x) (comm x))).comp
      (coneMapCochain (g x) (g y) ((M'.map x y).f p t) ((N'.map x y).f p t)) (zero_add p)
  have hm := congrArg (fun l => l.f p t) (hu x y)
  have hn := congrArg (fun l => l.f p t) (hv x y)
  change ((M.map x y).f p t).comp (Cochain.ofHom (u y)) (add_zero p) =
    (Cochain.ofHom (u x)).comp ((M'.map x y).f p t) (zero_add p) at hm
  change ((N.map x y).f p t).comp (Cochain.ofHom (v y)) (add_zero p) =
    (Cochain.ofHom (v x)).comp ((N'.map x y).f p t) (zero_add p) at hn
  rw [coneMapCochain_ofHom, coneMapCochain_ofHom,
    coneMapCochain_comp, coneMapCochain_comp, hm, hn]

variable (D) [Small.{u} D]

/-- 加群の可換 square は各評価で可換。 -/
lemma moduleSquare_eval {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (comm : f ≫ v = u ≫ g) (x : D) :
    (moduleEvaluation A D x).map f ≫ (moduleEvaluation A D x).map v =
      (moduleEvaluation A D x).map u ≫ (moduleEvaluation A D x).map g := by
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg (fun l => (moduleEvaluation A D x).map l) comm

/-- 実際の加群射からなる可換 square の cone 射。 -/
def moduleConeMap {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (comm : f ≫ v = u ≫ g) : moduleCone A D f ⟶ moduleCone A D g :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D g))
    (fun x => mappingCone.map ((moduleEvaluation A D x.unop).map f)
      ((moduleEvaluation A D x.unop).map g) ((moduleEvaluation A D x.unop).map u)
      ((moduleEvaluation A D x.unop).map v) (moduleSquare_eval A D f g u v comm x.unop))
    (coneFamilyMap_naturality A
      (closedTransApp A (moduleClosedHomEquiv A D M N f))
      (closedTransApp A (moduleClosedHomEquiv A D M' N' g))
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f))
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M' N' g))
      (closedTransApp A (moduleClosedHomEquiv A D M M' u))
      (closedTransApp A (moduleClosedHomEquiv A D N N' v))
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M M' u))
      (closedTransApp_naturality A (moduleClosedHomEquiv A D N N' v))
      (fun x => moduleSquare_eval A D f g u v comm x.unop))

/-- 評価した cone 射は既存 Mathlib の square の cone 射。 -/
@[simp] lemma moduleConeMap_eval {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (comm : f ≫ v = u ≫ g) (x : D) :
    (moduleEvaluation A D x).map (moduleConeMap A D f g u v comm) =
      mappingCone.map ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).map g)
        ((moduleEvaluation A D x).map u) ((moduleEvaluation A D x).map v)
          (moduleSquare_eval A D f g u v comm x) := by
  unfold moduleConeMap
  rw [moduleMorphismMk_eval]

/-- 恒等 square の cone 射は恒等射。 -/
lemma moduleConeMap_id {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeMap A D f f (𝟙 M) (𝟙 N) (by simp) = 𝟙 (moduleCone A D f) := by
  apply moduleMorphism_ext
  intro x
  simp only [moduleConeMap_eval, CategoryTheory.Functor.map_id]
  exact mappingCone.map_id _

/-- 可換 square の合成に対する cone 射の関手性。 -/
lemma moduleConeMap_comp {M N M' N' M'' N'' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (k : M'' ⟶ N'')
    (u : M ⟶ M') (v : N ⟶ N') (u' : M' ⟶ M'') (v' : N' ⟶ N'')
    (comm : f ≫ v = u ≫ g) (comm' : g ≫ v' = u' ≫ k) :
    moduleConeMap A D f k (u ≫ u') (v ≫ v')
      (by rw [← Category.assoc, comm, Category.assoc, comm', ← Category.assoc]) =
      moduleConeMap A D f g u v comm ≫ moduleConeMap A D g k u' v' comm' := by
  apply moduleMorphism_ext
  intro x
  simp only [moduleConeMap_eval, CategoryTheory.Functor.map_comp]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _
/-- 可換 square の cone 射は標準包含と可換。 -/
lemma moduleConeMap_inr {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (comm : f ≫ v = u ≫ g) :
    moduleConeInr A D f ≫ moduleConeMap A D f g u v comm = v ≫ moduleConeInr A D g := by
  apply moduleMorphism_ext
  intro x
  simp only [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeMap_eval]
  exact (mappingCone.triangleMap ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map u)
    ((moduleEvaluation A D x).map v) (moduleSquare_eval A D f g u v comm x)).comm₂

/-- 可換 square の cone 射は connecting map と可換。 -/
lemma moduleConeMap_connecting {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (comm : f ≫ v = u ≫ g) :
    moduleConeConnecting A D f ≫ u⟦(1 : ℤ)⟧' =
      moduleConeMap A D f g u v comm ≫ moduleConeConnecting A D g := by
  apply moduleMorphism_ext
  intro x
  simp only [CategoryTheory.Functor.map_comp, moduleConeConnecting_eval,
    moduleConeMap_eval, moduleShiftFunctor_eq, moduleShiftFunctor_map_eval]
  exact (mappingCone.triangleMap ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map u)
    ((moduleEvaluation A D x).map v) (moduleSquare_eval A D f g u v comm x)).comm₃

/-- 可換 square による加群の標準 cone triangle の射。 -/
def moduleConeTriangleMap {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (comm : f ≫ v = u ≫ g) : moduleConeTriangle A D f ⟶ moduleConeTriangle A D g where
  hom₁ := u
  hom₂ := v
  hom₃ := moduleConeMap A D f g u v comm
  comm₁ := comm
  comm₂ := moduleConeMap_inr A D f g u v comm
  comm₃ := moduleConeMap_connecting A D f g u v comm

/-- 閉零加群圏の arrow 圏からの cone 関手。 -/
def moduleConeFunctor : Arrow (ModuleCategory A D) ⥤ ModuleCategory A D where
  obj f := moduleCone A D f.hom
  map {f g} s := moduleConeMap A D f.hom g.hom s.left s.right s.w.symm
  map_id f := moduleConeMap_id A D f.hom
  map_comp {f g k} s t :=
    moduleConeMap_comp A D f.hom g.hom k.hom s.left s.right t.left t.right s.w.symm t.w.symm
end SerrePositivity.DifferentialGraded
