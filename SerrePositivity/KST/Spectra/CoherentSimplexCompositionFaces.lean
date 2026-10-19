module

public import SerrePositivity.KST.Spectra.CoherentSimplexTraceFaces
public import SerrePositivity.KST.Spectra.CoherentPathCompositionFaces

/-!
概要：coherent 三単体の Hom 正方形の一座標の二辺を、面の経路と豊穣合成で計算する。
方針：部分 path の合成式と元の豊穣関手の合成保存を使う。
規約：元の三単体の辺・面を保持。使われ方：円評価の四角形の零三角形の差の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の三単体の最初の辺の、定値な Hom 経路。 -/
def tetrahedronInitialTrace (σ : (SimplicialNerve C) _⦋3⦌) :
    (Δ[1] : SSet.{u}) ⟶
      SimplicialCategory.sHom (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 1⟩) :=
  constantPathParameter tetrahedronInitialPath ≫ σ.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩

/-- 元の三単体の最後の辺の、定値な Hom 経路。 -/
def tetrahedronFinalTrace (σ : (SimplicialNerve C) _⦋3⦌) :
    (Δ[1] : SSet.{u}) ⟶
      SimplicialCategory.sHom (σ.obj ⟨ULift.up 2⟩) (σ.obj ⟨ULift.up 3⟩) :=
  constantPathParameter tetrahedronFinalPath ≫ σ.map ⟨ULift.up 2⟩ ⟨ULift.up 3⟩

/-- 第一座標一の辺は、元の最初の辺と零番目の面の Hom 経路の豊穣合成。 -/
lemma tetrahedronTrace_includeFirst (σ : (SimplicialNerve C) _⦋3⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronTrace σ =
      lift (tetrahedronInitialTrace σ) (triangleTrace ((SimplicialNerve C).δ 0 σ)) ≫
        eComp SSet (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 1⟩) (σ.obj ⟨ULift.up 3⟩) := by
  rw [tetrahedronTrace, ← Category.assoc, tetrahedronPathSquare_includeFirst,
    Category.assoc, σ.map_comp, ← Category.assoc, lift_map]
  rfl

/-- 第二座標一の辺は、三番目の面の Hom 経路と元の最後の辺の豊穣合成。 -/
lemma tetrahedronTrace_includeSecond (σ : (SimplicialNerve C) _⦋3⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        tetrahedronTrace σ =
      lift (triangleTrace ((SimplicialNerve C).δ 3 σ)) (tetrahedronFinalTrace σ) ≫
        eComp SSet (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 2⟩) (σ.obj ⟨ULift.up 3⟩) := by
  rw [tetrahedronTrace, ← Category.assoc, tetrahedronPathSquare_includeSecond,
    Category.assoc, σ.map_comp, ← Category.assoc, lift_map]
  rfl

/-- 第一座標一の辺を、指定した零番目の面の経路と合成で表示する。 -/
lemma tetrahedronTrace_includeFirst_face {σ : (SimplicialNerve C) _⦋3⦌}
    {τ : (SimplicialNerve C) _⦋2⦌} (h : (SimplicialNerve C).δ 0 σ = τ) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronTrace σ =
      lift (tetrahedronInitialTrace σ)
        (triangleTrace τ ≫ eqToHom (congrArg
          (fun s : (SimplicialNerve C) _⦋2⦌ ↦
            SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)) h.symm)) ≫
        eComp SSet (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 1⟩) (σ.obj ⟨ULift.up 3⟩) := by
  rw [tetrahedronTrace_includeFirst, ← triangleTrace_congr h.symm]

/-- 第二座標一の辺を、指定した三番目の面の経路と合成で表示する。 -/
lemma tetrahedronTrace_includeSecond_face {σ : (SimplicialNerve C) _⦋3⦌}
    {τ : (SimplicialNerve C) _⦋2⦌} (h : (SimplicialNerve C).δ 3 σ = τ) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        tetrahedronTrace σ =
      lift (triangleTrace τ ≫ eqToHom (congrArg
          (fun s : (SimplicialNerve C) _⦋2⦌ ↦
            SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)) h.symm))
        (tetrahedronFinalTrace σ) ≫
        eComp SSet (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 2⟩) (σ.obj ⟨ULift.up 3⟩) := by
  rw [tetrahedronTrace_includeSecond, ← triangleTrace_congr h.symm]

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
