module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison


/-!
概要：可換 square の両辺の次数ごとの単射性を、実 cone の射へ運ぶ。
方針：cone の二つの次数付き射影と対角 cone 射の公式を使う。
規約：dg 加群のモデルと既存 cone は変更しない。
使われ方：D-8 d の部分セル付加と、全セル付加の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q P' Q' : Complex R}
  (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q') (h : f ≫ b = a ≫ g)

@[reassoc] lemma dgKappaConeMap_fst (n : ℤ) :
    (mappingCone.map f g a b h).f n ≫ (mappingCone.fst g).val.v n (n + 1) rfl =
      (mappingCone.fst f).val.v n (n + 1) rfl ≫ a.f (n + 1) := by
  have he := Cochain.congr_v (coneMapCochain_ofHom f g a b h) n n (add_zero n)
  rw [Cochain.ofHom_v] at he
  rw [he, coneMapCochain_fst_v]
  simp only [Int.negOnePow_zero, one_smul, Cochain.ofHom_v]

@[reassoc] lemma dgKappaConeMap_snd (n : ℤ) :
    (mappingCone.map f g a b h).f n ≫ (mappingCone.snd g).v n n (add_zero n) =
      (mappingCone.snd f).v n n (add_zero n) ≫ b.f n := by
  have he := Cochain.congr_v (coneMapCochain_ofHom f g a b h) n n (add_zero n)
  rw [Cochain.ofHom_v] at he
  rw [he, coneMapCochain_snd_v, Cochain.ofHom_v]

lemma dgKappaConeMap_degreewiseMono (n : ℤ) [Mono (a.f (n + 1))] [Mono (b.f n)] :
    Mono ((mappingCone.map f g a b h).f n) where
  right_cancellation s t he := by
    apply mappingCone.ext_to f n (n + 1) rfl
    · apply (cancel_mono (a.f (n + 1))).1
      rw [Category.assoc, Category.assoc, ← dgKappaConeMap_fst,
        ← Category.assoc, ← Category.assoc, he]
    · apply (cancel_mono (b.f n)).1
      rw [Category.assoc, Category.assoc, ← dgKappaConeMap_snd,
        ← Category.assoc, ← Category.assoc, he]

@[reassoc] lemma dgKappaConeMap_inl (n : ℤ) :
    (mappingCone.inl f).v (n + 1) n (by omega) ≫ (mappingCone.map f g a b h).f n =
      a.f (n + 1) ≫ (mappingCone.inl g).v (n + 1) n (by omega) := by
  have he := Cochain.congr_v (coneMapCochain_ofHom f g a b h) n n (add_zero n)
  rw [Cochain.ofHom_v] at he
  rw [he, coneMapCochain_inl_v]
  simp only [Int.negOnePow_zero, one_smul, Cochain.ofHom_v]

@[reassoc] lemma dgKappaConeMap_inr (n : ℤ) :
    (mappingCone.inr f).f n ≫ (mappingCone.map f g a b h).f n =
      b.f n ≫ (mappingCone.inr g).f n := by
  have he := congrArg (fun k => k.f n) (mappingCone.triangleMap f g a b h).comm₂
  simpa only [HomologicalComplex.comp_f] using! he

lemma dgKappaConeMap_element (n : ℤ) (u : P.X (n + 1)) (v : Q.X n) :
    (mappingCone.map f g a b h).f n
      ((mappingCone.inr f).f n v + (mappingCone.inl f).v (n + 1) n (by omega) u) =
      (mappingCone.inr g).f n (b.f n v) +
        (mappingCone.inl g).v (n + 1) n (by omega) (a.f (n + 1) u) := by
  rw [map_add]
  congr 1
  · simpa only [ModuleCat.comp_apply] using
      congrArg (fun k => k v) (dgKappaConeMap_inr f g a b h n)
  · simpa only [ModuleCat.comp_apply] using
      congrArg (fun k => k u) (dgKappaConeMap_inl f g a b h n)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgKappaModuleConeMap_comp {M N M' N' M'' N'' : ModuleCategory R D}
    (f : M ⟶ N) (g : M' ⟶ N') (k : M'' ⟶ N'')
    (u : M ⟶ M') (v : N ⟶ N') (u' : M' ⟶ M'') (v' : N' ⟶ N'')
    (U : M ⟶ M'') (V : N ⟶ N'')
    (h : f ≫ v = u ≫ g) (h' : g ≫ v' = u' ≫ k) (H : f ≫ V = U ≫ k)
    (hu : u ≫ u' = U) (hv : v ≫ v' = V) :
    moduleConeMap R D f g u v h ≫ moduleConeMap R D g k u' v' h' =
      moduleConeMap R D f k U V H := by
  subst U
  subst V
  exact (moduleConeMap_comp R D f g k u v u' v' h h').symm

lemma dgKappaModuleMap_mono {M N : ModuleCategory R D} (i : M ⟶ N)
    (hm : ∀ x n, Mono (((moduleEvaluation R D x).map i).f n)) : Mono i where
  right_cancellation a b h := by
    apply moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext n
    letI := hm x n
    apply (cancel_mono (((moduleEvaluation R D x).map i).f n)).1
    have he := congrArg (fun f => ((moduleEvaluation R D x).map f).f n) h
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using he

lemma dgKappaModuleConeMap_degreewiseMono {M N M' N' : ModuleCategory R D}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : f ≫ b = a ≫ g) (x : D) (n : ℤ)
    (ha : Mono (((moduleEvaluation R D x).map a).f (n + 1)))
    (hb : Mono (((moduleEvaluation R D x).map b).f n)) :
    Mono (((moduleEvaluation R D x).map (moduleConeMap R D f g a b h)).f n) := by
  rw [moduleConeMap_eval]
  letI := ha
  letI := hb
  exact dgKappaConeMap_degreewiseMono _ _ _ _ _ n

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
