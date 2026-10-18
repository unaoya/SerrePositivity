module

public import SerrePositivity.KST.Comparison.HomologyPairContraction
public import SerrePositivity.KST.Comparison.HomologyQuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-!
# 二段階収縮の鎖ホモトピー同値

概要：部分単体集合を保つ二段階収縮を実際の鎖ホモトピー同値へ移す。
方針：包含と終点を両逆とし、二つの区間写像の制限から両合成の鎖ホモトピーを作る。
規約：Waldhausen LNM 1126 §1.7・§1.8。任意の係数の horn 計算の準備。
使われ方：定数アーベル群係数の horn 包含の擬同型性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory MonoidalCategory
open scoped Simplicial

/--
概要：区間写像をその両端の間の単体的ホモトピーとして束ねる。
方針：端点の式は定義による等式とする。
規約：相対部分は空である。
使われ方：実際の係数鎖複体の鎖ホモトピー。
-/
def intervalMapSimplicialHomotopy {X Y : SSet.{u}}
    (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) : SSet.Homotopy (SSet.ι₀ ≫ h) (SSet.ι₁ ≫ h) where
  h := h
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/--
概要：二段階の対の収縮を、単体的ホモトピーを保つ鎖複体関手で鎖ホモトピー同値へ送る。
方針：収縮の終点を逆写像とし、制限した二つのホモトピーをつなぐ。
規約：係数関手のホモトピー保存を明示的に受け取る一般補題。
使われ方：実際の定数係数関手で用い、保存性は Mathlib の鎖ホモトピーを供給する。
-/
def chainHomotopyEquivOfPairContraction
    (K : SSet.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ)
    (hK : ∀ {Y Z : SSet.{u}} (h : Y ⊗ (Δ[1] : SSet.{u}) ⟶ Z),
      Homotopy (K.map (SSet.ι₀ ≫ h)) (K.map (SSet.ι₁ ≫ h)))
    {X : SSet.{u}} (A : X.Subcomplex)
    (h₀ h₁ : X ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀end : SSet.ι₁ ≫ h₀ = 𝟙 X) (hstart : SSet.ι₀ ≫ h₀ = SSet.ι₀ ≫ h₁)
    (h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d)
    (h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d)
    (hend : SSet.Subcomplex.range (SSet.ι₁ ≫ h₁) ≤ A) :
    HomotopyEquiv (K.obj (A : SSet.{u})) (K.obj X) := by
  let r := SSet.Subcomplex.lift (SSet.ι₁ ≫ h₁) hend
  let v₀ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀) (by
      rintro d x ⟨a, rfl⟩; exact h₀A d a.1 a.2)
  let v₁ : (A : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ A :=
    SSet.Subcomplex.lift (A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁) (by
      rintro d x ⟨a, rfl⟩; exact h₁A d a.1 a.2)
  have hv₀ : v₀ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₀ := rfl
  have hv₁ : v₁ ≫ A.ι = A.ι ▷ (Δ[1] : SSet.{u}) ≫ h₁ := rfl
  have he₀ : SSet.ι₁ ≫ v₀ = 𝟙 (A : SSet.{u}) := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, ← Category.assoc, SSet.ι₁_comp,
      Category.assoc, h₀end, Category.comp_id, Category.id_comp]
  have hs : SSet.ι₀ ≫ v₀ = SSet.ι₀ ≫ v₁ := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₀, Category.assoc, hv₁, ← Category.assoc,
      ← Category.assoc, SSet.ι₀_comp,
      Category.assoc, Category.assoc, hstart]
  have he₁ : SSet.ι₁ ≫ v₁ = A.ι ≫ r := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, hv₁, ← Category.assoc, SSet.ι₁_comp, Category.assoc]
    rfl
  refine {
    hom := K.map A.ι
    inv := K.map r
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_ }
  · refine (Homotopy.ofEq (K.map_comp A.ι r).symm).trans ?_
    refine (Homotopy.ofEq (congrArg K.map he₁.symm)).trans ?_
    refine (hK v₁).symm.trans ?_
    refine (Homotopy.ofEq (congrArg K.map hs.symm)).trans ?_
    refine (hK v₀).trans ?_
    exact Homotopy.ofEq ((congrArg K.map he₀).trans (K.map_id _))
  · refine (Homotopy.ofEq (K.map_comp r A.ι).symm).trans ?_
    change Homotopy (K.map (SSet.ι₁ ≫ h₁)) (𝟙 _)
    refine (hK h₁).symm.trans ?_
    refine (Homotopy.ofEq (congrArg K.map hstart.symm)).trans ?_
    refine (hK h₀).trans ?_
    exact Homotopy.ofEq ((congrArg K.map h₀end).trans (K.map_id _))

/--
概要：任意のアーベル群係数で二段階の対の収縮は鎖ホモトピー同値を誘導する。
方針：Mathlib の定数係数鎖複体の実際のホモトピー保存を一般補題へ供給する。
規約：係数の平坦性は必要としない。
使われ方：局所係数を自明化した後の horn の計算。
-/
def constantCoefficientChainHomotopyEquivOfPairContraction
    (G : AddCommGrpCat.{u}) {X : SSet.{u}} (A : X.Subcomplex)
    (h₀ h₁ : X ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀end : SSet.ι₁ ≫ h₀ = 𝟙 X) (hstart : SSet.ι₀ ≫ h₀ = SSet.ι₀ ≫ h₁)
    (h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d)
    (h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d)
    (hend : SSet.Subcomplex.range (SSet.ι₁ ≫ h₁) ≤ A) :
    HomotopyEquiv (A.toSSet.chainComplex G) (X.chainComplex G) :=
  chainHomotopyEquivOfPairContraction ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj G)
    (fun h => (intervalMapSimplicialHomotopy h).chainComplexMap G)
    A h₀ h₁ h₀end hstart h₀A h₁A hend

/--
概要：任意のアーベル群係数で horn 包含は実際の鎖ホモトピー同値を与える。
方針：horn を保つ二段階収縮を定数係数鎖複体へ適用する。
規約：正次元の horn。係数の平坦性を要求しない。
使われ方：標準単体上の局所係数を自明化した後の計算。
-/
def constantCoefficientHornChainHomotopyEquiv (G : AddCommGrpCat.{u})
    {d : ℕ} [NeZero d] (k : Fin (d + 1)) :
    HomotopyEquiv ((Λ[d, k] : SSet.{u}).chainComplex G) ((Δ[d] : SSet.{u}).chainComplex G) :=
  constantCoefficientChainHomotopyEquivOfPairContraction G (Λ[d, k])
    (simplexMeetToIdentity k).h (simplexMeetToVertex k).h
    (simplexMeetToIdentity k).h₁
    ((simplexMeetToIdentity k).h₀.trans (simplexMeetToVertex k).h₀.symm)
    (fun a s t => simplexMeetToIdentity_mem_horn k a s.val s.property t)
    (fun a s t => simplexMeetToVertex_mem_horn k a s.val s.property t)
    (by
      rintro a x ⟨s, rfl⟩
      rw [(simplexMeetToVertex k).h₁]
      exact const_horn_vertex_mem k a s)

/--
概要：任意の定数アーベル群係数で horn の鎖写像は擬同型である。
方針：構成した実際の鎖ホモトピー同値から導く。
規約：全ての正次元と horn。
使われ方：局所係数の horn 添付の基礎。
-/
theorem constantCoefficientHorn_quasiIso (G : AddCommGrpCat.{u})
    {d : ℕ} [NeZero d] (k : Fin (d + 1)) :
    QuasiIso (SSet.chainComplexMap (Λ[d, k] : (Δ[d] : SSet.{u}).Subcomplex).ι G) :=
  (constantCoefficientHornChainHomotopyEquiv G k).quasiIso_hom

end SerrePositivity.KST.Comparison
