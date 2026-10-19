module

public import SerrePositivity.InfinityCategories.F2.JoinSummands
public import SerrePositivity.InfinityCategories.F2.ConstantPrism
public import SerrePositivity.InfinityCategories.F2.SpecifiedHomotopyLift
public import SerrePositivity.InfinityCategories.F2.PrismHomotopy
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：頂点と指定された図式の prism を保つ極限錐の輸送。
方針：二因子の和への制限に沿って可逆ホモトピーを持ち上げる。
規約：標的は quasicategory、形状には充填性を仮定しない。
使われ方：Cat_∞ の引き戻しの二脚の具体的な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：錐の頂点を固定する prism と指定された図式の prism を貼る。
方針：join の二因子の和の上で coproduct の貼り合わせを使う。
規約：錐の内部の混合単体はこの段階では指定しない。
使われ方：元の図式と置換後の図式の錐を比較する。 -/
def coneBoundaryPrism {K X : SSet.{u}} {q : K ⟶ X}
    (d : JoinCone q) (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ ((Δ[0] : SSet.{u}) ⨿ K) ⟶ X :=
  coprodPrism (snd Δ[1] Δ[0] ≫ joinInl Δ[0] K ≫ d.val) H
/-- 概要：指定した可逆 prism に沿って頂点を固定した極限錐を輸送する。
方針：join の二因子の和への制限でホモトピーを厳密に持ち上げる。
規約：頂点の定値ホモトピーと図式の指定 prism を全時刻で保持する。
使われ方：引き戻し錐の二射影と指定自然変換の照合。 -/
lemma exists_limitCone_of_specifiedPrism {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (h₀ : prismEndpoint 0 K ≫ H = p) (h₁ : prismEndpoint 1 K ≫ H = q)
    (hH : ∀ x : K _⦋0⦌, IsInvertibleEdge (edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))))
    (d : JoinCone q) (hd : IsLimitCone d) :
    ∃ c : JoinCone p, IsLimitCone c ∧ c.vertex = d.vertex ∧
      ∃ G : SSet.Homotopy c.val d.val,
        (coprod.desc (joinInl Δ[0] K) (joinInr Δ[0] K) ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          (β_ ((Δ[0] : SSet.{u}) ⨿ K) (Δ[1] : SSet.{u})).hom ≫ coneBoundaryPrism d H ∧
        ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge G x).toTruncated := by
  let i := coprod.desc (joinInl (Δ[0] : SSet.{u}) K) (joinInr Δ[0] K)
  let f := coprod.desc (joinInl (Δ[0] : SSet.{u}) K ≫ d.val) p
  have hb₀ : prismEndpoint 0 ((Δ[0] : SSet.{u}) ⨿ K) ≫ coneBoundaryPrism d H = f := by
    rw [coneBoundaryPrism, coprodPrism_endpoint, constantPrism_endpoint, h₀]
  have hb₁ : prismEndpoint 1 ((Δ[0] : SSet.{u}) ⨿ K) ≫ coneBoundaryPrism d H = i ≫ d.val := by
    rw [coneBoundaryPrism, coprodPrism_endpoint, constantPrism_endpoint, h₁]
    apply coprod.hom_ext <;> simp [i, d.property]
  let Hb := prismHomotopy (coneBoundaryPrism d H) hb₀ hb₁
  have hi : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge Hb x).toTruncated := by
    intro x
    refine (isInvertibleEdge_congr
      (e := (simplicialHomotopyVertexEdge Hb x).toTruncated)
      (f := edgeOfSimplex ((coneBoundaryPrism d H).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) ?_).mpr ?_
    · exact prismHomotopy_vertical _ hb₀ hb₁ x
    · exact coprodPrism_vertical_isInvertible _ H (constantPrism_vertical_isInvertible _) hH x
  obtain ⟨w, G, hw, hG, hGi⟩ := exists_mono_homotopy_lift_target i f d.val Hb hi
  have hw₀ : joinInl (Δ[0] : SSet.{u}) K ≫ w = joinInl Δ[0] K ≫ d.val := by
    have h := congrArg (fun t ↦ (coprod.inl : Δ[0] ⟶ Δ[0] ⨿ K) ≫ t) hw
    simpa only [i, f, ← Category.assoc, coprod.inl_desc] using h
  have hw₁ : joinInr (Δ[0] : SSet.{u}) K ≫ w = p := by
    have h := congrArg (fun t ↦ (coprod.inr : K ⟶ Δ[0] ⨿ K) ≫ t) hw
    simpa only [i, f, ← Category.assoc, coprod.inr_desc] using h
  let c : JoinCone p := ⟨w, hw₁⟩
  refine ⟨c, ?_, ?_, G, hG, hGi⟩
  · exact IsLimitCone.of_functorIso hd (functorIsoOfPointwiseInvertibleHomotopy G hGi).symm
  · exact congrArg SSet.yonedaEquiv hw₀

end SerrePositivity.InfinityCategories.F2
