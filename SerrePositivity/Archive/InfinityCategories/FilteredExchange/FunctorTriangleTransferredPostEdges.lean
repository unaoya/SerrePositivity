module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleStrictPostThreeEdges

/-!
概要：同じ指定三角形比較の三辺の表示を、明示した共通頂点と同じ指定値へ移す。
方針：元の中間・終点の等式で逆と後合成を輸送し、三辺の厳密な表示へ合成する。
規約：HEq から頂点等式を取り出さない。使われ方：四面を同じ六辺の比較へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "va" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)
local notation "vb" => leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)
local notation "vc" => leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)
local notation "Pa" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection G) (Subtype.val va) (Subtype.property va) p
local notation "Pb" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J) (Subtype.val vb) (Subtype.property vb) p
local notation "Pc" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection J) (Subtype.val vc) (Subtype.property vc) p
local notation "x₀" => relativeFunctorVertex (leftUnstraighteningProjection F) p s hi

/-- 元の三角形比較は、明示した共通二頂点と同じ三つの指定値へ移しても厳密な三辺表示を保つ。 -/
lemma FunctorTrianglePointedWitness.sequentialPostComparison_app_eq_transferredEdges
    (x₁ : (relativeFunctorSpace (leftUnstraighteningProjection G) p) _⦋0⦌)
    (x₂ : (relativeFunctorSpace (leftUnstraighteningProjection J) p) _⦋0⦌)
    (eₐ : VertexIso ((Pa).app _ x₀) x₁) (eᵦ : VertexIso ((Pb).app _ x₁) x₂)
    (e𝒸 : VertexIso ((Pc).app _ x₀) x₂)
    (h₁ : relativeFunctorVertex (leftUnstraighteningProjection G) p
      w.middle w.middle_projection = x₁)
    (h₂ : relativeFunctorVertex (leftUnstraighteningProjection J) p
      w.endpoint w.endpoint_projection = x₂)
    (hₐ : HEq (functorHomotopySourcePostIso a p s hi w.firstWitness) eₐ)
    (hᵦ : HEq (functorHomotopySourcePostIso b p w.middle w.middle_projection w.secondWitness) eᵦ)
    (h𝒸 : HEq (functorHomotopySourcePostIso c p s hi w.longWitness) e𝒸) :
    (functorTriangleSequentialPostComparison T p).app x₀ =
      e𝒸 ≪≫ eᵦ.symm ≪≫ VertexIso.map eₐ.symm Pb := by
  let a₀ := functorHomotopySourcePostIso a p s hi w.firstWitness
  let b₀ := functorHomotopySourcePostIso b p w.middle w.middle_projection w.secondWitness
  let c₀ := functorHomotopySourcePostIso c p s hi w.longWitness
  have ha' := vertexIso_symm_heq_of_heq a₀ eₐ rfl h₁ hₐ
  have hb' := vertexIso_symm_heq_of_heq b₀ eᵦ
    (congrArg (fun v => (Pb).app (Opposite.op ⦋0⦌) v) h₁) h₂ hᵦ
  have hm := vertexIso_map_heq_of_heq a₀.symm eₐ.symm h₁ rfl ha' Pb
  have ht := vertexIso_trans_heq_of_heq b₀.symm (VertexIso.map a₀.symm Pb)
    eᵦ.symm (VertexIso.map eₐ.symm Pb) h₂
    (congrArg (fun v => (Pb).app (Opposite.op ⦋0⦌) v) h₁) rfl hb' hm
  have h := vertexIso_trans_heq_of_heq c₀ (b₀.symm ≪≫ VertexIso.map a₀.symm Pb)
    e𝒸 (eᵦ.symm ≪≫ VertexIso.map eₐ.symm Pb) rfl h₂ rfl h𝒸 ht
  exact (w.sequentialPostComparison_app_eq_threeEdges hi).trans (eq_of_heq h)

end SerrePositivity.InfinityCategories.F2
