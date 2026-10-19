module

public import SerrePositivity.KST.Spectra.CoherentSimplexTraces
public import SerrePositivity.KST.Spectra.CoherentPathParameterFaces

/-!
概要：coherent 三単体の Hom 正方形の二辺を、元の二単体の Hom 経路へ同定する。
方針：内点を欠く path の添字変換を、元の豊穣関手の前合成に移す。
規約：面と端点の移送を明示する。使われ方：円の元の三単体と生成 loop の比較。
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

/-- 第一座標零の辺は、一番目の面の元の Hom 経路。 -/
lemma tetrahedronTrace_skipFirst (σ : (SimplicialNerve C) _⦋3⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        tetrahedronTrace σ = triangleTrace ((SimplicialNerve C).δ 1 σ) := by
  rw [tetrahedronTrace, ← Category.assoc, tetrahedronPathSquare_skipFirst, Category.assoc]
  rfl

/-- 第二座標零の辺は、二番目の面の元の Hom 経路。 -/
lemma tetrahedronTrace_skipSecond (σ : (SimplicialNerve C) _⦋3⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        tetrahedronTrace σ = triangleTrace ((SimplicialNerve C).δ 2 σ) := by
  rw [tetrahedronTrace, ← Category.assoc, tetrahedronPathSquare_skipSecond, Category.assoc]
  rfl

/-- 二単体の等式は、端点を移送した元の Hom 経路の等式を与える。 -/
lemma triangleTrace_congr {σ τ : (SimplicialNerve C) _⦋2⦌} (h : σ = τ) :
    triangleTrace σ ≫ eqToHom (congrArg
        (fun s : (SimplicialNerve C) _⦋2⦌ ↦
          SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)) h) =
      triangleTrace τ := by
  cases h
  exact Category.comp_id _


/-- 同じ二単体の経路は、共通の Hom へ端点を移送しても一致する。 -/
lemma triangleTrace_transport {σ τ : (SimplicialNerve C) _⦋2⦌} (h : σ = τ)
    {T : SSet.{u}}
    (hσ : SimplicialCategory.sHom (σ.obj ⟨ULift.up 0⟩) (σ.obj ⟨ULift.up 2⟩) = T)
    (hτ : SimplicialCategory.sHom (τ.obj ⟨ULift.up 0⟩) (τ.obj ⟨ULift.up 2⟩) = T) :
    triangleTrace σ ≫ eqToHom hσ = triangleTrace τ ≫ eqToHom hτ := by
  cases h
  rfl

/-- 二番目の面を指定した二単体へ同定し、元の Hom 正方形の端点だけを正規化する。 -/
def tetrahedronTraceAgainst {σ : (SimplicialNerve C) _⦋3⦌}
    {τ : (SimplicialNerve C) _⦋2⦌} (h : (SimplicialNerve C).δ 2 σ = τ) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      SimplicialCategory.sHom (τ.obj ⟨ULift.up 0⟩) (τ.obj ⟨ULift.up 2⟩) :=
  tetrahedronTrace σ ≫ eqToHom (congrArg
    (fun s : (SimplicialNerve C) _⦋2⦌ ↦
      SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)) h)

/-- 正規化した正方形の第二座標零の辺は、指定した二単体の元の Hom 経路。 -/
lemma tetrahedronTraceAgainst_skipSecond {σ : (SimplicialNerve C) _⦋3⦌}
    {τ : (SimplicialNerve C) _⦋2⦌} (h : (SimplicialNerve C).δ 2 σ = τ) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        tetrahedronTraceAgainst h = triangleTrace τ := by
  rw [tetrahedronTraceAgainst, ← Category.assoc, tetrahedronTrace_skipSecond,
    triangleTrace_congr h]

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
