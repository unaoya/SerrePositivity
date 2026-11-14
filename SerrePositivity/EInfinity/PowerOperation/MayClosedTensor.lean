module

public import SerrePositivity.EInfinity.PowerOperation.MaySphereHomotopy
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-!
# May の境界表示のための閉テンソルの類

May, Proposition 2.3(ii) の補助。
閉テンソルの自然性と、一方のホモロジー類が零ならテンソルの類も零であること。
後者は sphere 射の実鎖ホモトピーをテンソルし、平坦性を仮定せずに示す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {k : Type u} [CommRing k]

/-- 閉同次元の純テンソルを、実際の全複体の閉元として保持する。 -/
def mayClosedTensor {K L : Complex k} (i j : ℤ) (a : MayClosed K i) (b : MayClosed L j) :
    MayClosed (cochainTensor K L) (i + j) :=
  ⟨ιTensorObj K L i j (i + j) rfl (a.val ⊗ₜ[k] b.val), by
    change (cochainTensor K L).d (i + j) (i + j + 1)
      (ιTensorObj K L i j (i + j) rfl (a.val ⊗ₜ[k] b.val)) = 0
    rw [cochainTensor_d_apply_ι, show K.d i (i + 1) a.val = 0 from a.property,
      show L.d j (j + 1) b.val = 0 from b.property]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
    change (ιTensorObj K L _ _ _ _).hom 0 +
      i.negOnePow • (ιTensorObj K L _ _ _ _).hom 0 = 0
    simp only [map_zero, smul_zero, add_zero]⟩

lemma mayClosedTensor_map {K K' L L' : Complex k} (f : K ⟶ K') (g : L ⟶ L')
    (i j : ℤ) (a : MayClosed K i) (b : MayClosed L j) :
    mayClosedMap (cochainTensorMap f g) (i + j) (mayClosedTensor i j a b) =
      mayClosedTensor i j (mayClosedMap f i a) (mayClosedMap g j b) := by
  apply Subtype.ext
  exact cochainTensorMap_apply_ι f g i j (i + j) rfl a.val b.val

lemma maySphereMap_zero (K : Complex k) (i : ℤ) :
    (complexSphereHomEquiv k K i).symm (0 : MayClosed K i) = 0 := by
  apply (complexSphereHomEquiv k K i).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rfl

/-- 閉テンソルの左因子の類が零なら、元の全複体でのテンソルの類も零。 -/
lemma mayClosedTensor_class_zero_left {K L : Complex k} (i j : ℤ)
    (a : MayClosed K i) (b : MayClosed L j) (ha : mayClosedClass K i a = 0) :
    mayClosedClass (cochainTensor K L) (i + j) (mayClosedTensor i j a b) = 0 := by
  let f := (complexSphereHomEquiv k K i).symm a
  let g := (complexSphereHomEquiv k L j).symm b
  let u : MayClosed (complexSphere k i) i := complexSphereHomEquiv k (complexSphere k i) i (𝟙 _)
  let v : MayClosed (complexSphere k j) j := complexSphereHomEquiv k (complexSphere k j) j (𝟙 _)
  have H := maySphereHomotopy K i a 0 (ha.trans (map_zero (mayClosedClass K i)).symm)
  have Ht := cochainTensorHomotopyLeft H g
  have hm := Ht.homologyMap_eq (i + j)
  rw [maySphereMap_zero, cochainTensorMap_zero_left, homologyMap_zero] at hm
  have hv : mayClosedMap (cochainTensorMap f g) (i + j) (mayClosedTensor i j u v) =
      mayClosedTensor i j a b := by
    rw [mayClosedTensor_map]
    exact congrArg₂ (mayClosedTensor i j) (maySphereGenerator_map K i a)
      (maySphereGenerator_map L j b)
  have hn := mayClosedClass_naturality (cochainTensorMap f g) (i + j) (mayClosedTensor i j u v)
  rw [hv] at hn
  change homologyMap (cochainTensorMap f g) (i + j) = 0 at hm
  rw [hm] at hn
  exact hn.symm.trans (by rfl)

end SerrePositivity.EInfinity.PowerOperation
