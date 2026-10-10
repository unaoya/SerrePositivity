module

public import SerrePositivity.CategoryTheory.KaroubiPretriangulated
public import SerrePositivity.CategoryTheory.OctahedronPadding
public import SerrePositivity.CategoryTheory.OctahedronEssentialImage

/-! # Karoubi 包絡の八面体公理

Balmer–Schlichting, Theorem 1.12 の証明に従う。
自明な三角形を加えて三頂点を元の圏に戻し、その八面体から retract を取る。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- 標準的な前三角構造を備えた Karoubi 包絡は八面体公理を満たす。 -/
instance karoubiIsTriangulated : IsTriangulated (Karoubi C) where
  octahedron_axiom {X Y Z U V W u v w} comm {a b} h₁ {c d} h₂ {e f} h₃ := by
    let A := X.complement
    let B := Y.complement
    let D := Z.complement
    have hX : (toKaroubi C).essImage (X ⊞ A) := ⟨X.X, ⟨X.decomposition.symm⟩⟩
    have hY : (toKaroubi C).essImage (Y ⊞ B) := ⟨Y.X, ⟨Y.decomposition.symm⟩⟩
    have hZ : (toKaroubi C).essImage (Z ⊞ D) := ⟨Z.X, ⟨Z.decomposition.symm⟩⟩
    obtain ⟨H⟩ := nonempty_octahedron_of_essImage (toKaroubi C)
      (paddedTriangle_comp comm A B D)
      (paddedTriangle_distinguished _ h₁ A B)
      (paddedTriangle_distinguished _ h₂ B D)
      (paddedTriangle_distinguished _ h₃ A D) hX hY hZ
    exact ⟨octahedronOfPadding comm h₁ h₂ h₃ A B D H
      (fun _ _ h r ↦ karoubiDistinguished_retract h r)⟩

end SerrePositivity
