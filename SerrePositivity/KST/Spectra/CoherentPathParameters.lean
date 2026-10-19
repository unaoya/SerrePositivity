module

public import SerrePositivity.KST.Spectra.CoherentFlaggedPaths

/-!
概要：二単体の長い Hom を区間で、三単体の長い Hom を正方形でパラメーター化する。
方針：各単体の頂点の二値フラグを path の包含列へ移す。
規約：全ての面と退化に自然。使われ方：元の円評価の三単体の Hom 内の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 区間の一単体列を、二単体の長い Hom の path の包含列へ移す。 -/
def trianglePathChain {d : ℕ} (a : (Δ[1] : SSet.{u}) _⦋d⦌) :
    Fin (d + 1) ⥤ Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) where
  obj i := flaggedPath (fun _ : Fin 1 ↦ a i)
  map f := flaggedPathMap (fun _ ↦ stdSimplex.monotone_apply a (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 二単体の長い Hom の、元の path の包含による区間パラメーター。 -/
def trianglePathInterval : (Δ[1] : SSet.{u}) ⟶
    nerve (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) where
  app _ := ↾trianglePathChain
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro a
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    exact Subsingleton.elim _ _

/-- 二つの座標を、二つの内点の二値フラグとして保持する。 -/
def twoFlags (a b : Fin 2) : Fin 2 → Fin 2 := fun r ↦ if r = 0 then a else b

/-- 正方形の単体列を、三単体の長い Hom の path の包含列へ移す。 -/
def tetrahedronPathChain {d : ℕ} (a b : (Δ[1] : SSet.{u}) _⦋d⦌) :
    Fin (d + 1) ⥤ Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) where
  obj i := flaggedPath (twoFlags (a i) (b i))
  map {i j} f := flaggedPathMap (fun r ↦ by
    by_cases h : r = 0
    · simpa only [twoFlags, h, ↓reduceIte] using stdSimplex.monotone_apply a (leOfHom f)
    · simpa only [twoFlags, h, ↓reduceIte] using stdSimplex.monotone_apply b (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 三単体の長い Hom の、元の path の包含による正方形パラメーター。 -/
def tetrahedronPathSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve (Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)) where
  app _ := ↾fun ab ↦ tetrahedronPathChain ab.1 ab.2
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro ab
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    exact Subsingleton.elim _ _

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
