module
public import SerrePositivity.DifferentialGraded.Module.ContractibleTriangleIso

/-! # K(D)の標準coneによるdistinguished三角形のクラス

回転と八面体の証明前にはPretriangulated/Triangulatedのインスタンスを置かない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDistinguishedTriangles : Set (Triangle (ModuleHomotopyCategory A D)) :=
  {T | ∃ (M N : ModuleCategory A D) (f : M ⟶ N),
    Nonempty (T ≅ moduleHomotopyConeTriangle A D f)}

lemma moduleHomotopyConeTriangle_distinguished {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomotopyConeTriangle A D f ∈ moduleDistinguishedTriangles A D :=
  ⟨M, N, f, ⟨Iso.refl _⟩⟩

lemma moduleDistinguished_isomorphic (T₁ : Triangle (ModuleHomotopyCategory A D))
    (hT₁ : T₁ ∈ moduleDistinguishedTriangles A D)
    (T₂ : Triangle (ModuleHomotopyCategory A D)) (e : T₂ ≅ T₁) :
    T₂ ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M, N, f, ⟨e'⟩⟩ := hT₁
  exact ⟨M, N, f, ⟨e ≪≫ e'⟩⟩

lemma moduleDistinguished_cocone {M N : ModuleHomotopyCategory A D} (f : M ⟶ N) :
    ∃ (T : ModuleHomotopyCategory A D) (g : N ⟶ T) (h : T ⟶ M⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  exact ⟨_, _, _, moduleHomotopyConeTriangle_distinguished A D f⟩

lemma moduleDistinguished_contractible (M : ModuleHomotopyCategory A D) :
    contractibleTriangle M ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M⟩ := M
  refine ⟨M, M, 𝟙 M, ⟨?_⟩⟩
  exact moduleHomotopyIdentityConeTriangleIso A D M

lemma moduleDistinguished_complete (T₁ T₂ : Triangle (ModuleHomotopyCategory A D))
    (hT₁ : T₁ ∈ moduleDistinguishedTriangles A D) (hT₂ : T₂ ∈ moduleDistinguishedTriangles A D)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨M, N, f, ⟨e₁⟩⟩ := hT₁
  obtain ⟨M', N', g, ⟨e₂⟩⟩ := hT₂
  let a' := e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁
  let b' := e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂
  have hf : (moduleToHomotopy A D).map f ≫ b' = a' ≫ (moduleToHomotopy A D).map g := by
    dsimp [a', b']
    have h₁ := e₁.inv.comm₁
    have h₂ := e₂.hom.comm₁
    change (moduleToHomotopy A D).map f ≫ e₁.inv.hom₂ = e₁.inv.hom₁ ≫ T₁.mor₁ at h₁
    change T₂.mor₁ ≫ e₂.hom.hom₂ = e₂.hom.hom₁ ≫ (moduleToHomotopy A D).map g at h₂
    simp only [reassoc_of% h₁, reassoc_of% fac, h₂, Category.assoc]
  obtain ⟨t, ht₁, ht₂⟩ := moduleHomotopyConeTriangle_complete A D f g a' b' hf
  let γ := e₁.hom ≫ t ≫ e₂.inv
  have hγ₁ : γ.hom₁ = a := by
    change e₁.hom.hom₁ ≫ t.hom₁ ≫ e₂.inv.hom₁ = a
    rw [ht₁]
    dsimp only [a']
    simp only [Category.assoc, Iso.hom_inv_id_triangle_hom₁_assoc,
      Iso.hom_inv_id_triangle_hom₁, Category.comp_id]
  have hγ₂ : γ.hom₂ = b := by
    change e₁.hom.hom₂ ≫ t.hom₂ ≫ e₂.inv.hom₂ = b
    rw [ht₂]
    dsimp only [b']
    simp only [Category.assoc, Iso.hom_inv_id_triangle_hom₂_assoc,
      Iso.hom_inv_id_triangle_hom₂, Category.comp_id]
  refine ⟨γ.hom₃, ?_, ?_⟩
  · simpa only [hγ₂] using γ.comm₂
  · simpa only [hγ₁] using γ.comm₃


@[reassoc] lemma moduleDistinguished_comp_zero₁₂
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.mor₁ ≫ T.mor₂ = 0 := by
  obtain ⟨c, hc, _⟩ := moduleDistinguished_complete A D
    (contractibleTriangle T.obj₁) T (moduleDistinguished_contractible A D T.obj₁) hT
    (𝟙 T.obj₁) T.mor₁ rfl
  simpa only [contractibleTriangle_mor₂, zero_comp] using hc.symm

end SerrePositivity.DifferentialGraded
