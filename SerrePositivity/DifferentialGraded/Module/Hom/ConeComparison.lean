module

public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import Mathlib.CategoryTheory.Comma.Arrow
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy

/-!
# Module.Hom.ConeComparison

## 概要
cone・cylinder と全次数 Hom の比較、前後合成をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## ConeMaps（旧 SerrePositivity/DifferentialGraded/Module/ConeMaps.lean） -/

/-! # cone の connecting map と objectwise triangle -/

@[expose] public section ConeMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存 cone triangle の connecting map を全次数自然な加群射へ持ち上げる。 -/
def moduleConeConnecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A D f ⟶ M⟦(1 : ℤ)⟧ :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (N := shiftModule 1 (ForgetEnrichment.to (Complex A) M))
    (fun x => (mappingCone.triangle
      (closedTransApp A (moduleClosedHomEquiv A D M N f) x)).mor₃) (by
        intro x y
        exact coneHomMap_connecting _ _ _ _
          (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f) x y))

/-- connecting map の評価は既存複体 cone triangle の第三射。 -/
@[simp] lemma moduleConeConnecting_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeConnecting A D f) =
      (mappingCone.triangle ((moduleEvaluation A D x).map f)).mor₃ := by
  unfold moduleConeConnecting
  rw [moduleMorphismMk_eval]
  rfl

/-- 加群圏の標準 cone triangle。distinguished の主張はホモトピー/導来圏で行う。 -/
def moduleConeTriangle {M N : ModuleCategory A D} (f : M ⟶ N) : Triangle (ModuleCategory A D) :=
  Triangle.mk f (moduleConeInr A D f) (moduleConeConnecting A D f)

/-- 評価した標準 cone triangle と既存複体の標準 triangle の比較。 -/
def moduleConeTriangleEvaluationIso {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).mapTriangle.obj (moduleConeTriangle A D f) ≅
      mappingCone.triangle ((moduleEvaluation A D x).map f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [moduleConeTriangle, Functor.mapTriangle_obj, Triangle.mk_mor₁,
      mappingCone.triangle_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [moduleConeTriangle, Functor.mapTriangle_obj, Triangle.mk_mor₂,
      mappingCone.triangle_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp,
      moduleConeInr_eval])
    (by
      simp only [moduleConeTriangle, Functor.mapTriangle_obj, Triangle.mk_mor₃,
        Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
        moduleConeConnecting_eval]
      change (mappingCone.triangle ((moduleEvaluation A D x).map f)).mor₃ =
        (mappingCone.triangle ((moduleEvaluation A D x).map f)).mor₃ ≫ 𝟙 _
      rw [Category.comp_id])
end SerrePositivity.DifferentialGraded
end

end ConeMaps

/-! ## ConeFunctor（旧 SerrePositivity/DifferentialGraded/Module/ConeFunctor.lean） -/

/-! # 可換 square の cone 射と関手性 -/

@[expose] public section ConeFunctor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end ConeFunctor

/-! ## ConeGradedSplit（旧 SerrePositivity/DifferentialGraded/Module/ConeGradedSplit.lean） -/

/-! # cone付加の全次数作用に関する分裂 -/

@[expose] public section ConeGradedSplit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleConeInr_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A D f ≫ moduleConeConnecting A D f = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeConnecting_eval,
    CategoryTheory.Functor.map_zero]
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    complexConeGradedProjection_eq_connecting, complexConeGradedProjection,
    Preadditive.comp_neg, mappingCone.inr_f_fst_v, neg_zero]

/-- cone拡大 N→cone(f)→M[1] は微分を忘れた全次数加群で分裂する。 -/
def moduleConeGradedSplit {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleGradedSplit A D (moduleConeInr A D f) (moduleConeConnecting A D f) where
  retraction x n := complexConeGradedRetraction ((moduleEvaluation A D x).map f) n
  section_ x n := complexConeGradedSection ((moduleEvaluation A D x).map f) n
  inclusion_retraction x n := by
    rw [moduleConeInr_eval]
    exact complexConeGradedRetraction_inr _ n
  section_projection x n := by
    rw [moduleConeConnecting_eval, complexConeGradedProjection_eq_connecting]
    exact complexConeGradedSection_connecting _ n
  section_retraction x n := complexConeGradedSection_retraction _ n
  inclusion_projection := moduleConeInr_connecting A D f
  decomposition x n := by
    rw [moduleConeInr_eval, moduleConeConnecting_eval, complexConeGradedProjection_eq_connecting]
    exact complexConeGraded_decomposition _ n
  retraction_naturality x y p i j hij a := by
    exact coneMapCochain_snd_v _ _ _ _ i j hij
  section_naturality x y p i j hij a := by
    exact complexConeGradedSection_naturality _ _ _ _ i j hij

lemma moduleConeInr_mono {M N : ModuleCategory A D} (f : M ⟶ N) :
    Mono (moduleConeInr A D f) := (moduleConeGradedSplit A D f).mono

lemma moduleConeConnecting_epi {M N : ModuleCategory A D} (f : M ⟶ N) :
    Epi (moduleConeConnecting A D f) := (moduleConeGradedSplit A D f).epi

/-- cone付加の商は主dg加群圏でM[1]。 -/
def moduleConeInrCokernel {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsColimit (CokernelCofork.ofπ (moduleConeConnecting A D f) (moduleConeInr_connecting A D f)) :=
  moduleGradedSplitCokernel A D (moduleConeGradedSplit A D f)

end SerrePositivity.DifferentialGraded
end

end ConeGradedSplit

/-! ## ConeElements（旧 SerrePositivity/DifferentialGraded/Module/ConeElements.lean） -/

/-! # coneの包含・射影を主Hom endの斉次要素として構成

左包含は次数−1、第一射影は次数+1、第二射影は次数0である。
微分と全dg自然性をともに保持する。
-/

@[expose] public section ConeElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeInlElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X (-1) :=
  moduleHomElementMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f)) (-1)
    (fun x => mappingCone.inl ((moduleEvaluation A D x.unop).map f)) (by
      intro x y p a
      apply Cochain.ext
      intro i j hij
      obtain ⟨k, rfl⟩ : ∃ k : ℤ, i = k + 1 := ⟨i - 1, by omega⟩
      rw [Cochain.units_smul_v,
        Cochain.comp_v _ _ _ (k + 1) (j + 1) j (by omega) (by omega),
        Cochain.comp_v _ _ _ (k + 1) k j (by omega) (by omega)]
      change _ = (-1 * p).negOnePow •
        ((mappingCone.inl ((moduleEvaluation A D x.unop).map f)).v (k + 1) k (by omega) ≫
          (coneMapCochain ((moduleEvaluation A D x.unop).map f)
            ((moduleEvaluation A D y.unop).map f)
            (((ForgetEnrichment.to (Complex A) M).map x y).f p a)
            (((ForgetEnrichment.to (Complex A) N).map x y).f p a)).v k j (by omega))
      rw [coneMapCochain_inl_v]
      simp only [neg_one_mul, Int.negOnePow_neg, smul_smul, Int.units_mul_self, one_smul])


lemma moduleConeInlElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f (-1)
        (moduleConeInlElement A D f) = mappingCone.inl ((moduleEvaluation A D x).map f) :=
  moduleHomElementMk_π A D (-1) _ _ x

def moduleConeFstElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) M)).X 1 :=
  moduleHomElementMk A D (M := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (N := ForgetEnrichment.to (Complex A) M) 1
    (fun x => (mappingCone.fst ((moduleEvaluation A D x.unop).map f)).val) (by
      intro x y p a
      apply Cochain.ext
      intro i j hij
      rw [Cochain.units_smul_v,
        Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
        Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega)]
      have h := Cochain.congr_v (coneMapCochain_fst
        ((moduleEvaluation A D x.unop).map f) ((moduleEvaluation A D y.unop).map f)
        (((ForgetEnrichment.to (Complex A) M).map x y).f p a)
        (((ForgetEnrichment.to (Complex A) N).map x y).f p a)) i j (by omega)
      rw [Cochain.units_smul_v,
        Cochain.comp_v _ _ rfl i (i + p) j rfl (by omega),
        Cochain.comp_v _ _ (by omega : 1 + p = p + 1) i (i + 1) j rfl (by omega)] at h
      change (coneMapCochain ((moduleEvaluation A D x.unop).map f)
        ((moduleEvaluation A D y.unop).map f)
        (((ForgetEnrichment.to (Complex A) M).map x y).f p a)
        (((ForgetEnrichment.to (Complex A) N).map x y).f p a)).v i (i + p) rfl ≫
          (mappingCone.fst ((moduleEvaluation A D y.unop).map f)).val.v (i + p) j (by omega) = _
      simpa only [one_mul] using h)


lemma moduleConeFstElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) M) x).f 1 (moduleConeFstElement A D f) =
        (mappingCone.fst ((moduleEvaluation A D x).map f)).val :=
  moduleHomElementMk_π A D 1 _ _ x

def moduleConeSndElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) N)).X 0 :=
  (moduleConeGradedSplit A D f).retractionElement

lemma moduleConeSndElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) N) x).f 0 (moduleConeSndElement A D f) =
        mappingCone.snd ((moduleEvaluation A D x).map f) := by
  rw [moduleConeSndElement, ModuleGradedSplit.retractionElement_π]
  rfl

lemma moduleConeInlElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
        (moduleConeInlElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (f ≫ moduleConeInr A D f))).val := by
  apply moduleHomElement_ext A D
    (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
  intro x
  rw [moduleHomElement_d_π, moduleConeInlElement_π, mappingCone.δ_inl,
    ← moduleEvaluation_cochain, CategoryTheory.Functor.map_comp, moduleConeInr_eval]

lemma moduleConeFstElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) M)).d 1 2 (moduleConeFstElement A D f) = 0 := by
  apply moduleHomElement_ext A D
    (M := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (N := ForgetEnrichment.to (Complex A) M)
  intro x
  rw [moduleHomElement_d_π, moduleConeFstElement_π, map_zero]
  exact Cocycle.δ_eq_zero _ _

end SerrePositivity.DifferentialGraded
end

end ConeElements

/-! ## ConeTransportIso（旧 SerrePositivity/DifferentialGraded/Module/ConeTransportIso.lean） -/

/-!
概要：両端の閉同型を持つ可換四角形から、実 cone の同型を得る。
方針：arrow 圏の同型を標準 cone 関手へ送る。
規約：元の四角形の射と両端同型を保持する。
使われ方：巨大な延長値の型展開を避ける、表示 cone の評価比較。
-/

@[expose] public section ConeTransportIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeIsoOfSquare {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ≅ M') (b : N ≅ N')
    (h : a.hom ≫ g = f ≫ b.hom) :=
  (moduleConeFunctor A D).mapIso (Arrow.isoMk' f g a b h)

end SerrePositivity.DifferentialGraded
end

end ConeTransportIso

/-! ## Cylinder（旧 SerrePositivity/DifferentialGraded/Module/Cylinder.lean） -/

/-! # 全 dg 自然な加群 cylinder とホモトピーの延長

単位複体の標準cylinderをtensorし、左単位比較で元の加群に接続する。
射影は任意可換環上でobjectwise準同型。モデル構造やflatnessを仮定しない。
-/

@[expose] public section Cylinder
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex HomotopicalAlgebra
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意加群の標準pre-cylinder。全作用はintervalとのtensorから得る。 -/
def modulePrecylinder (M : ModuleCategory A D) : Precylinder M where
  I := ForgetEnrichment.of (Complex A)
    (tensorModule (dgInterval A) (ForgetEnrichment.to (Complex A) M))
  i₀ := (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₀ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)
  i₁ := (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₁ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)
  π := tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
    (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom
  i₀_π := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleTensorUnitIso_inv_eval, moduleTensorUnitIso_hom_eval, tensorModuleMap_eval,
      Category.assoc, tensorHom_id]
    rw [← comp_whiskerRight_assoc, cylinder.ι₀_π, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id]
  i₁_π := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleTensorUnitIso_inv_eval, moduleTensorUnitIso_hom_eval, tensorModuleMap_eval,
      Category.assoc, tensorHom_id]
    rw [← comp_whiskerRight_assoc, cylinder.ι₁_π, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id]

/-- 標準cylinderの射影はobjectwise quasiIso。 -/
lemma modulePrecylinder_π_quasiIso (M : ModuleCategory A D) :
    moduleQuasiIso A D (modulePrecylinder A D M).π := by
  intro x
  change QuasiIso ((moduleEvaluation A D x).map
    (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom))
  rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, moduleTensorUnitIso_hom_eval]
  exact tensorIntervalProjection_quasiIso A _

/-- 全 dg 自然なホモトピーを加群cylinderからの射へ延長する。 -/
def moduleCylinderDesc {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).I ⟶ N :=
  moduleParamUncurry A D (cylinder.desc
    (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f)
    (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) g) h.some)

lemma moduleCylinderDesc_i₀ {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).i₀ ≫ moduleCylinderDesc A D f g h = f := by
  change ((moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₀ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)) ≫
      moduleParamUncurry A D (cylinder.desc _ _ h.some) = f
  rw [Category.assoc, moduleParamUncurry_precomp, cylinder.ι₀_desc, moduleParamUncurry_closed,
    Iso.inv_hom_id_assoc]

lemma moduleCylinderDesc_i₁ {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).i₁ ≫ moduleCylinderDesc A D f g h = g := by
  change ((moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₁ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)) ≫
      moduleParamUncurry A D (cylinder.desc _ _ h.some) = g
  rw [Category.assoc, moduleParamUncurry_precomp, cylinder.ι₁_desc, moduleParamUncurry_closed,
    Iso.inv_hom_id_assoc]

/-- Mathlib LeftHomotopy の具体的証人。 -/
def moduleCylinderLeftHomotopy {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).LeftHomotopy f g where
  h := moduleCylinderDesc A D f g h
  h₀ := moduleCylinderDesc_i₀ A D f g h
  h₁ := moduleCylinderDesc_i₁ A D f g h

end SerrePositivity.DifferentialGraded
end

end Cylinder

/-! ## Precomposition（旧 SerrePositivity/DifferentialGraded/Module/Precomposition.lean） -/

/-! # 前合成の全次数転置と全dg自然なホモトピーの像

次数pの前合成は入力次数qについてKoszul符号を含む豊穣順合成である。
-/

@[expose] public section Precomposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def modulePrecompositionMap (M N T : RightModule A D) :
    moduleHom A D M N ⟶ homComplex A (moduleHom A D N T) (moduleHom A D M T) :=
  curryRight (moduleComposition A D M N T)

lemma modulePrecompositionMap_apply (M N T : RightModule A D) {p q n : ℤ}
    (g : (moduleHom A D M N).X p) (z : (moduleHom A D N T).X q)
    (hn : q + p = n) :
    (((modulePrecompositionMap A D M N T).f p g).v q n hn) z =
      forward A (x := M) (y := N) (z := T) g z (by omega) := rfl

lemma modulePrecompositionMap_d (M N T : RightModule A D) (p r : ℤ)
    (g : (moduleHom A D M N).X p) :
    δ p r ((modulePrecompositionMap A D M N T).f p g) =
      (modulePrecompositionMap A D M N T).f r ((moduleHom A D M N).d p r g) :=
  congrArg (fun a => a g) ((modulePrecompositionMap A D M N T).comm p r)

lemma modulePrecompositionMap_closed {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D) :
    (modulePrecompositionMap A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom (eHomWhiskerRight (Complex A) f T) := by
  apply Cochain.ext₀
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((modulePrecompositionMap A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val).v q q (add_zero q)) z =
        (eHomWhiskerRight (Complex A) f T).f q z
  rw [modulePrecompositionMap_apply]
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomForward_π, zero_mul, Int.negOnePow_zero, one_smul,
    ← moduleEvaluation_cochain]
  exact (moduleHomWhiskerRight_apply_π A D f q z x).symm

def moduleHomPrecomposeHomotopy {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (T : ModuleCategory A D) :
    Homotopy (eHomWhiskerRight (Complex A) f T) (eHomWhiskerRight (Complex A) g T) := by
  let H := modulePrecompositionMap A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T)
  have hd := modulePrecompositionMap_d A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) T) (-1) 0 h.val
  change δ (-1) 0 (H.f (-1) h.val) =
    H.f 0 ((homObject A (RightModule A D) M N).d (-1) 0 h.val) at hd
  rw [h.property, map_sub, modulePrecompositionMap_closed,
    modulePrecompositionMap_closed] at hd
  refine (Cochain.equivHomotopy _ _).symm ⟨H.f (-1) h.val, ?_⟩
  exact (sub_eq_iff_eq_add).1 hd.symm

end SerrePositivity.DifferentialGraded
end

end Precomposition

/-! ## Postcomposition（旧 SerrePositivity/DifferentialGraded/Module/Postcomposition.lean） -/

/-! # 全次数の後合成をHom複体間のcochainへ転置する -/

@[expose] public section Postcomposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomWhiskerLeft_apply_π {T M N : ModuleCategory A D} (f : M ⟶ N)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f q
        ((eHomWhiskerLeft (Complex A) T f).f q z) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) x).f q z).comp
          (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero q) :=
  congrArg (fun a => a.f q z) (moduleHomWhiskerLeft_π A D (M := T) f x)

lemma moduleHomCompose_π {T M N : RightModule A D} {p q n : ℤ}
    (g : (moduleHom A D M N).X p) (z : (moduleHom A D T M).X q)
    (hn : q + p = n) (x : D) :
    (moduleHomπ A D T N x).f n (compose A (x := T) (y := M) (z := N) g z hn) =
      ((moduleHomπ A D T M x).f q z).comp ((moduleHomπ A D M N x).f p g) hn := by
  unfold compose
  simp only [Units.smul_def, map_zsmul]
  change (q * p).negOnePow •
    (moduleHomπ A D T N x).f n (forward A (x := T) (y := M) (z := N) z g hn) = _
  rw [moduleHomForward_π, smul_smul, Int.units_mul_self, one_smul]

def modulePostcompositionMap (T M N : RightModule A D) :
    moduleHom A D M N ⟶ homComplex A (moduleHom A D T M) (moduleHom A D T N) :=
  curryRight ((β_ (moduleHom A D M N) (moduleHom A D T M)).hom ≫
    moduleComposition A D T M N)

lemma modulePostcompositionMap_apply (T M N : RightModule A D) {p q n : ℤ}
    (g : (moduleHom A D M N).X p) (z : (moduleHom A D T M).X q)
    (hn : q + p = n) :
    (((modulePostcompositionMap A D T M N).f p g).v q n hn) z =
      compose A (x := T) (y := M) (z := N) g z hn := by
  change (moduleComposition A D T M N).f n
    ((signedSwap (moduleHom A D M N) (moduleHom A D T M)).hom.f n
      (ιTensorObj (moduleHom A D M N) (moduleHom A D T M) p q n (by omega) (g ⊗ₜ[A] z))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • forward A (x := T) (y := M) (z := N) z g hn = _
  rw [compose, mul_comm p q]

lemma modulePostcompositionMap_d (T M N : RightModule A D) (p r : ℤ)
    (g : (moduleHom A D M N).X p) :
    δ p r ((modulePostcompositionMap A D T M N).f p g) =
      (modulePostcompositionMap A D T M N).f r ((moduleHom A D M N).d p r g) :=
  congrArg (fun a => a g) ((modulePostcompositionMap A D T M N).comm p r)

lemma modulePostcompositionMap_closed (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (modulePostcompositionMap A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom (eHomWhiskerLeft (Complex A) T f) := by
  apply Cochain.ext₀
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((modulePostcompositionMap A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val).v q q (add_zero q)) z =
        (eHomWhiskerLeft (Complex A) T f).f q z
  rw [modulePostcompositionMap_apply]
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
    (N := ForgetEnrichment.to (Complex A) N)
  intro x
  rw [moduleHomCompose_π, ← moduleEvaluation_cochain]
  exact (congrArg (fun a => a.f q z) (moduleHomWhiskerLeft_π A D (M := T) f x)).symm

end SerrePositivity.DifferentialGraded
end

end Postcomposition

/-! ## HomCone（旧 SerrePositivity/DifferentialGraded/Module/HomCone.lean） -/

/-! # 主Hom endと標準coneの比較射

左包含の微分公式を転置して、Mathlibのconeのdescを適用する。
-/

@[expose] public section HomCone
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleHomConeLeftCochain (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    Homogeneous (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M))
      (moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f))) (-1) :=
  (modulePostcompositionMap A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f (-1)
      (moduleConeInlElement A D f)

lemma moduleHomConeLeftCochain_d (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) : δ (-1) 0 (moduleHomConeLeftCochain A D T f) =
      Cochain.ofHom (eHomWhiskerLeft (Complex A) T f ≫
        eHomWhiskerLeft (Complex A) T (moduleConeInr A D f)) := by
  rw [moduleHomConeLeftCochain, modulePostcompositionMap_d, moduleConeInlElement_d,
    modulePostcompositionMap_closed, eHomWhiskerLeft_comp]

lemma moduleHomConeLeftCochain_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q n : ℤ) (hn : q + (-1) = n)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f n
        ((moduleHomConeLeftCochain A D T f).v q n hn z) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) x).f q z).comp
          (mappingCone.inl ((moduleEvaluation A D x).map f)) hn := by
  rw [moduleHomConeLeftCochain, modulePostcompositionMap_apply, moduleHomCompose_π,
    moduleConeInlElement_π]

def moduleHomConeComparison (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    mappingCone (eHomWhiskerLeft (Complex A) T f) ⟶
      moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) :=
  mappingCone.desc (eHomWhiskerLeft (Complex A) T f) (moduleHomConeLeftCochain A D T f)
    (eHomWhiskerLeft (Complex A) T (moduleConeInr A D f))
    (moduleHomConeLeftCochain_d A D T f)

@[reassoc] lemma moduleHomConeComparison_inr (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr (eHomWhiskerLeft (Complex A) T f) ≫ moduleHomConeComparison A D T f =
      eHomWhiskerLeft (Complex A) T (moduleConeInr A D f) :=
  mappingCone.inr_desc _ _ _ _

lemma moduleHomConeComparison_apply_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ) (z : (mappingCone (eHomWhiskerLeft (Complex A) T f)).X q)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q
        ((moduleHomConeComparison A D T f).f q z) =
      mappingCone.liftCochain ((moduleEvaluation A D x).map f)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) M) x).f (q + 1)
            ((mappingCone.fst (eHomWhiskerLeft (Complex A) T f)).val.v q (q + 1) rfl z))
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N) x).f q
            ((mappingCone.snd (eHomWhiskerLeft (Complex A) T f)).v q q (add_zero q) z)) rfl := by
  rw [moduleHomConeComparison,
    mappingCone.desc_f _ _ _ _ q (q + 1) rfl]
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q
      ((moduleHomConeLeftCochain A D T f).v (q + 1) q (by omega)
        ((mappingCone.fst (eHomWhiskerLeft (Complex A) T f)).val.v q (q + 1) rfl z) +
       (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
         (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q from
         (eHomWhiskerLeft (Complex A) T (moduleConeInr A D f)).f q
           ((mappingCone.snd (eHomWhiskerLeft (Complex A) T f)).v q q (add_zero q) z))) = _
  rw [map_add, moduleHomConeLeftCochain_π, moduleHomWhiskerLeft_apply_π, moduleConeInr_eval]
  rfl

end SerrePositivity.DifferentialGraded
end

end HomCone

/-! ## HomConeIso（旧 SerrePositivity/DifferentialGraded/Module/HomConeIso.lean） -/

/-! # 主Hom endはconeを複体のconeへ同型に送る -/

@[expose] public section HomConeIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleHomConeInverseElement (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q) :
    (mappingCone (eHomWhiskerLeft (Complex A) T f)).X q :=
  complexConeElementMk A (eHomWhiskerLeft (Complex A) T f) q
    (compose A (x := ForgetEnrichment.to (Complex A) T)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) M) (moduleConeFstElement A D f) z rfl)
    (compose A (x := ForgetEnrichment.to (Complex A) T)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) N) (moduleConeSndElement A D f) z (add_zero q))

lemma moduleHomConeInverseElement_fst_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f (q + 1)
        ((mappingCone.fst (eHomWhiskerLeft (Complex A) T f)).val.v q (q + 1) rfl
          (moduleHomConeInverseElement A D T f q z)) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q z).comp
          (mappingCone.fst ((moduleEvaluation A D x).map f)).val rfl := by
  rw [moduleHomConeInverseElement, complexConeElementMk_fst, moduleHomCompose_π,
    moduleConeFstElement_π]

lemma moduleHomConeInverseElement_snd_π (T : ModuleCategory A D) {M N : ModuleCategory A D}
    (f : M ⟶ N) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f q
        ((mappingCone.snd (eHomWhiskerLeft (Complex A) T f)).v q q (add_zero q)
          (moduleHomConeInverseElement A D T f q z)) =
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q z).comp
          (mappingCone.snd ((moduleEvaluation A D x).map f)) (add_zero q) := by
  rw [moduleHomConeInverseElement, complexConeElementMk_snd, moduleHomCompose_π,
    moduleConeSndElement_π]

lemma moduleHomConeComparison_rightInverse (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.RightInverse (moduleHomConeInverseElement A D T f q)
      ((moduleHomConeComparison A D T f).f q) := by
  intro z
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
  intro x
  rw [moduleHomConeComparison_apply_π, moduleHomConeInverseElement_fst_π,
    moduleHomConeInverseElement_snd_π]
  apply (mappingCone.ext_cochain_to_iff ((moduleEvaluation A D x).map f) q (q + 1) rfl).2
  exact ⟨mappingCone.liftCochain_fst _ _ _ _, mappingCone.liftCochain_snd _ _ _ _⟩

lemma moduleHomConeComparison_leftInverse (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.LeftInverse (moduleHomConeInverseElement A D T f q)
      ((moduleHomConeComparison A D T f).f q) := by
  intro z
  apply complexConeElement_ext A (eHomWhiskerLeft (Complex A) T f) q
  · apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
      (N := ForgetEnrichment.to (Complex A) M)
    intro x
    rw [moduleHomConeInverseElement_fst_π, moduleHomConeComparison_apply_π,
      mappingCone.liftCochain_fst]
  · apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
      (N := ForgetEnrichment.to (Complex A) N)
    intro x
    rw [moduleHomConeInverseElement_snd_π, moduleHomConeComparison_apply_π,
      mappingCone.liftCochain_snd]

lemma moduleHomConeComparison_bijective (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.Bijective ((moduleHomConeComparison A D T f).f q) :=
  ⟨(moduleHomConeComparison_leftInverse A D T f q).injective,
    (moduleHomConeComparison_rightInverse A D T f q).surjective⟩

instance moduleHomConeComparison_isIso (T : ModuleCategory A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) : IsIso (moduleHomConeComparison A D T f) := by
  let (q : ℤ) : IsIso ((moduleHomConeComparison A D T f).f q) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (moduleHomConeComparison_bijective A D T f q)
  exact HomologicalComplex.Hom.isIso_of_components _

def moduleHomConeIso (T : ModuleCategory A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone (eHomWhiskerLeft (Complex A) T f) ≅
      moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) :=
  asIso (moduleHomConeComparison A D T f)

end SerrePositivity.DifferentialGraded
end

end HomConeIso

/-! ## HomCycles（旧 SerrePositivity/DifferentialGraded/Module/HomCycles.lean） -/

/-! # 主Hom endの閉次数零要素と加群射の合成 -/

@[expose] public section HomCycles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleMorphismOfCycle {M N : ModuleCategory A D}
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).X 0)
    (hz : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 z = 0) : M ⟶ N :=
  (closedHomEquiv A (RightModule A D) M N).symm ⟨z, hz⟩

lemma moduleMorphismOfCycle_cycle {M N : ModuleCategory A D} (z) (hz) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
      (moduleMorphismOfCycle A D (M := M) (N := N) z hz))).val = z :=
  congrArg Subtype.val ((closedHomEquiv A (RightModule A D) M N).apply_symm_apply ⟨z, hz⟩)

lemma moduleHomCycle_postcompose {T M N : ModuleCategory A D} (g : T ⟶ M) (f : M ⟶ N) :
    (eHomWhiskerLeft (Complex A) T f).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (g ≫ f))).val := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
    (N := ForgetEnrichment.to (Complex A) N)
  intro x
  rw [moduleHomWhiskerLeft_apply_π, ← moduleEvaluation_cochain A D x g,
    ← moduleEvaluation_cochain A D x (g ≫ f), CategoryTheory.Functor.map_comp,
    Cochain.ofHom_comp]

end SerrePositivity.DifferentialGraded
end

end HomCycles

/-! ## HomClosedInsertion（旧 SerrePositivity/DifferentialGraded/Module/HomClosedInsertion.lean） -/

/-!
概要：斉次合成の中間の閉零加群射を、前の Hom の後合成と後の Hom の制限の間で移す。
方針：各評価の cochain に戻し、中間次数零の結合則を使う。
規約：全ての斉次次数と元の閉零射を保持する。
使われ方：bar の各 summand の包含を通じて二乗項を各列に移す。
-/

@[expose] public section HomClosedInsertion
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomClosedInsertion {S M N P : ModuleCategory R D} (i : M ⟶ N)
    {p q n : ℤ}
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) S)
      (ForgetEnrichment.to (Complex R) M)).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X q) (h : p + q = n) :
    compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P)
        g ((eHomWhiskerLeft (Complex R) S i).f p f) h =
      compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) P)
        ((eHomWhiskerRight (Complex R) i P).f q g) f h := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) S) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomCompose_π R D, moduleHomCompose_π R D,
    moduleHomWhiskerLeft_apply_π R D (T := S) (M := M) (N := N) i p f x,
    moduleHomWhiskerRight_apply_π R D (M := M) (N := N) (P := P) i q g x]
  exact Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ h

end SerrePositivity.DifferentialGraded
end

end HomClosedInsertion

/-! ## HomRestrictionComposition（旧 SerrePositivity/DifferentialGraded/Module/HomRestrictionComposition.lean） -/

/-!
概要：閉零加群射による全次数 Hom の制限は通常順の斉次合成と可換。
方針：元の評価成分へ戻し、次数零 cochain を先頭に置く結合則を使う。
規約：元の閉射と全次数 Hom を保持し、h 圏だけの等式には弱めない。
使われ方：coherent bar の MC 方程式を各 summand の列へ制限する。
-/

@[expose] public section HomRestrictionComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomRestriction_compose {S M N P : ModuleCategory R D} (i : S ⟶ M)
    {p q n : ℤ}
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X q) (h : p + q = n) :
    (eHomWhiskerRight (Complex R) i P).f n
        (compose R (x := ForgetEnrichment.to (Complex R) M)
          (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P)
          g f h) =
      compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P)
        g ((eHomWhiskerRight (Complex R) i N).f p f) h := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) S) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomWhiskerRight_apply_π R D (M := S) (N := M) (P := P) i n _ x,
    moduleHomCompose_π R D (T := ForgetEnrichment.to (Complex R) M)
      (M := ForgetEnrichment.to (Complex R) N) (N := ForgetEnrichment.to (Complex R) P),
    moduleHomCompose_π R D (T := ForgetEnrichment.to (Complex R) S)
      (M := ForgetEnrichment.to (Complex R) N) (N := ForgetEnrichment.to (Complex R) P),
    moduleHomWhiskerRight_apply_π R D (M := S) (N := M) (P := N) i p _ x]
  exact (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ h).symm

end SerrePositivity.DifferentialGraded
end

end HomRestrictionComposition

/-! ## HomPostcompositionComposition（旧 SerrePositivity/DifferentialGraded/Module/HomPostcompositionComposition.lean） -/

/-!
概要：全次数の加群 Hom の斉次合成は、閉零射による後合成と両立する。
方針：各加群評価の cochain へ戻し、次数零の第三射との結合則を使う。
規約：元の加群と全次数を保持する。
使われ方：bar のシフトブロックを元の余積包含へ送る計算。
-/

@[expose] public section HomPostcompositionComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomPostcomposition_compose {S M N P : ModuleCategory R D} (i : N ⟶ P)
    {p q n : ℤ}
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) S)
      (ForgetEnrichment.to (Complex R) M)).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X q) (h : p + q = n) :
    compose R (x := ForgetEnrichment.to (Complex R) S)
      (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) P)
      ((eHomWhiskerLeft (Complex R) M i).f q g) f h =
    (eHomWhiskerLeft (Complex R) S i).f n
      (compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) N)
        g f h) := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) S) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomCompose_π R D,
    moduleHomWhiskerLeft_apply_π R D (T := M) (M := N) (N := P) i q g x,
    moduleHomWhiskerLeft_apply_π R D (T := S) (M := N) (N := P) i n
      (compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) N) g f h) x,
    moduleHomCompose_π R D]
  exact (Cochain.comp_assoc_of_third_is_zero_cochain
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) S)
      (ForgetEnrichment.to (Complex R) M) x).f p f)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N) x).f q g)
    (Cochain.ofHom ((moduleEvaluation R D x).map i)) h).symm

end SerrePositivity.DifferentialGraded
end

end HomPostcompositionComposition
