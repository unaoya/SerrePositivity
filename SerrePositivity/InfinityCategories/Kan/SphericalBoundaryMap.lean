module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.SphericalBoundaryFilling
public import SerrePositivity.InfinityCategories.Kan.BoundaryFaces

/-!
概要：球面的な面族を境界射へ貼り、交代和でその充填を判定する。
方針：境界の面の余極限と Kan 充填による球面的境界の判定を合成する。
規約：標準単体の次元は三以上。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の付着境界に適用する界面。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SphericalBoundary
end SerrePositivity.KST.Spectra.SphericalBoundary
namespace SerrePositivity.InfinityCategories.Kan.SphericalBoundary
open _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary

noncomputable section

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

/-- 概要：球面的な面族は全ての二面の交叉で互換である。
方針：各面の境界が同じ基点に定数であることを使う。
規約：Kan 性は不要。
使われ方：Goerss–Jardine I §7。境界の面の貼り合わせ。 -/
theorem facesCompatible (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.IsCompatible (fun j ↦ (a j).map) := fun _ _ _ ↦ by simp

/-- 概要：球面的な面族からの実際の境界射。
方針：互換な面の multicoequalizer の降下を使う。
規約：境界は ∂Δ[n+3]。
使われ方：Goerss–Jardine I §7、VIII §1。セルの境界の障害計算。 -/
def boundaryMap (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    (∂Δ[n + 3] : SSet.{u}) ⟶ X := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.desc (_root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.facesCompatible a)

/-- 概要：貼り合わせた境界射の各面は指定した単体。
方針：境界の余極限の標準射の計算を使う。
規約：任意の面の添字。
使われ方：Goerss–Jardine I §7。全境界と面族の比較。 -/
@[reassoc (attr := simp)]
theorem face_boundaryMap (a : Fin (n + 4) → X.PtSimplex (n + 2) x) (j : Fin (n + 4)) :
    boundary.ι j ≫ _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.boundaryMap a = (a j).map := _root_.SerrePositivity.InfinityCategories.Kan.BoundaryFaces.ι_desc _ _

/-- 概要：球面的な面族の充填と、その境界射の充填は同値。
方針：境界射の等式を各面へ制限し、逆向きは面での外延性を使う。
規約：この比較に Kan 性は不要。
使われ方：Goerss–Jardine I §7。幾何的な単体の存在を通常の境界延長へ移す。 -/
theorem nonempty_iff_boundary_filler (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary a) ↔
      ∃ f : (Δ[n + 3] : SSet.{u}) ⟶ X, (boundary (n + 3)).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.boundaryMap a := by
  constructor
  · rintro ⟨T⟩
    refine ⟨T.map, ?_⟩
    apply boundary.hom_ext
    intro j
    rw [boundary.ι_ι_assoc, T.face_eq, _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.face_boundaryMap]
  · rintro ⟨f, hf⟩
    refine ⟨{_root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.map := f, _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.face_eq := ?_}⟩
    intro j
    rw [← boundary.ι_ι_assoc, hf, _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.face_boundaryMap]

/-- 概要：球面的な境界射が充填できることはホモトピー類の交代和の零性と同値。
方針：面族と境界射の充填の比較に、Kan ホーンからの判定を適用する。
規約：実際の単体的な射の存在を結論する。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の障害消滅の実現。 -/
theorem boundary_filler_iff [KanComplex X]
    (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    (∃ f : (Δ[n + 3] : SSet.{u}) ⟶ X, (boundary (n + 3)).ι ≫ f = _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.boundaryMap a) ↔
      _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.alternatingClass a = 0 :=
  (_root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.nonempty_iff_boundary_filler a).symm.trans (_root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.nonempty_iff_alternatingClass_eq_zero a)

end

end SerrePositivity.InfinityCategories.Kan.SphericalBoundary

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.boundaryMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.boundaryMap := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.boundaryMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.boundary_filler_iff := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.boundary_filler_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.face_boundaryMap := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.face_boundaryMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.face_boundaryMap_assoc := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.face_boundaryMap_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.facesCompatible := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.facesCompatible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.nonempty_iff_boundary_filler := _root_.SerrePositivity.InfinityCategories.Kan.SphericalBoundary.nonempty_iff_boundary_filler
