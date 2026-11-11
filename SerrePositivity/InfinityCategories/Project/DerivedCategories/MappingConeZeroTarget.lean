module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # 零終域の mapping cone と一回シフト

概要：零対象への鎖写像の標準 cone 接続射は複体の同型である。
方針：各次数の cone を二項直和と比較し、零な第二成分を落とす。
規約：接続射は Mathlib の負の第一射影。使われ方：D7 の suspension と複体シフトの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B : Complex S}

/-- 第二成分が零なら二項直和の第一射影は同型。 -/
lemma biprod_fst_isIso_of_isZero {V : Type*} [Category V] [Preadditive V]
    (X Y : V) [HasBinaryBiproduct X Y] (hY : IsZero Y) :
    IsIso (biprod.fst : X ⊞ Y ⟶ X) := by
  refine ⟨⟨biprod.inl, ?_, biprod.inl_fst⟩⟩
  apply biprod.hom_ext
  · simp
  · exact hY.eq_of_tgt _ _

/-- 零終域の cone の接続射は複体同型。 -/
lemma mappingCone_connecting_isIso_of_isZero (f : A ⟶ B) (hB : IsZero B) :
    IsIso (mappingCone.triangle f).mor₃ := by
  suffices hh : ∀ n, IsIso ((mappingCone.triangle f).mor₃.f n) by
    let := hh
    exact HomologicalComplex.Hom.isIso_of_components _
  intro n
  have hBn : IsZero (B.X n) := (HomologicalComplex.eval _ _ n).map_isZero hB
  have : IsIso (biprod.fst : A.X (n + 1) ⊞ B.X n ⟶ A.X (n + 1)) :=
    biprod_fst_isIso_of_isZero _ _ hBn
  have hf : IsIso ((mappingCone.fst f).val.v n (n + 1) rfl) := by
    change IsIso ((HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).hom ≫
      (biprod.fst : A.X (n + 1) ⊞ B.X n ⟶ A.X (n + 1)))
    infer_instance
  change IsIso (((-mappingCone.fst f).val.rightShift 1 0 (zero_add 1)).v n n (add_zero n))
  rw [Cochain.rightShift_v _ 1 0 (zero_add 1) n n (add_zero n) (n + 1) rfl]
  simp only [Cocycle.coe_neg, Cochain.neg_v]
  have : IsIso (-((mappingCone.fst f).val.v n (n + 1) rfl)) :=
    ⟨⟨-inv ((mappingCone.fst f).val.v n (n + 1) rfl), by simp, by simp⟩⟩
  infer_instance

/-- 零終域の標準 cone の一回シフトへの同型。 -/
def mappingConeZeroTargetIso (f : A ⟶ B) (hB : IsZero B) : mappingCone f ≅ A⟦(1 : ℤ)⟧ := by
  have := mappingCone_connecting_isIso_of_isZero f hB
  exact asIso (mappingCone.triangle f).mor₃

/-- 零終域の cone 接続同型は可換正方形に対して自然。 -/
lemma mappingConeZeroTargetIso_naturality {A' B' : Complex S}
    (f : A ⟶ B) (g : A' ⟶ B') (hB : IsZero B) (hB' : IsZero B')
    (a : A ⟶ A') (b : B ⟶ B') (comm : f ≫ b = a ≫ g) :
    mappingCone.map f g a b comm ≫ (mappingConeZeroTargetIso g hB').hom =
      (mappingConeZeroTargetIso f hB).hom ≫ a⟦(1 : ℤ)⟧' :=
  (mappingCone.triangleMap f g a b comm).comm₃.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
