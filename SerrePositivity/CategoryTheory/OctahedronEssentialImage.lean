module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # 完全忠実な三角関手の本質像上の八面体 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.Full] [F.Faithful] [F.CommShift ℤ] [F.IsTriangulated]

omit [F.Faithful] in
/-- 合成する二つの射の三頂点が本質像にあれば、元の圏の八面体を移せる。 -/
lemma nonempty_octahedron_of_essImage
    {X Y Z U V W : D} {u : X ⟶ Y} {v : Y ⟶ Z} {w : X ⟶ Z}
    (comm : u ≫ v = w)
    {a : Y ⟶ U} {b : U ⟶ X⟦(1 : ℤ)⟧} (h₁ : Triangle.mk u a b ∈ distTriang D)
    {c : Z ⟶ V} {d : V ⟶ Y⟦(1 : ℤ)⟧} (h₂ : Triangle.mk v c d ∈ distTriang D)
    {e : Z ⟶ W} {f : W ⟶ X⟦(1 : ℤ)⟧} (h₃ : Triangle.mk w e f ∈ distTriang D)
    (hX : F.essImage X) (hY : F.essImage Y) (hZ : F.essImage Z) :
    Nonempty (Octahedron comm h₁ h₂ h₃) := by
  obtain ⟨X', ⟨iX⟩⟩ := hX
  obtain ⟨Y', ⟨iY⟩⟩ := hY
  obtain ⟨Z', ⟨iZ⟩⟩ := hZ
  let u' := F.preimage (iX.hom ≫ u ≫ iY.inv)
  let v' := F.preimage (iY.hom ≫ v ≫ iZ.inv)
  obtain ⟨_, _, _, h₁'⟩ := distinguished_cocone_triangle u'
  obtain ⟨_, _, _, h₂'⟩ := distinguished_cocone_triangle v'
  obtain ⟨_, _, _, h₃'⟩ := distinguished_cocone_triangle (u' ≫ v')
  exact ⟨Octahedron.ofIso (e₁ := iX.symm) (e₂ := iY.symm) (e₃ := iZ.symm)
    (comm₁₂ := by simp [u']) (comm₂₃ := by simp [v'])
    (H := (someOctahedron rfl h₁' h₂' h₃').map F) ..⟩

end SerrePositivity
