module

public import SerrePositivity.KST.DerivedGeometry.EmbeddedChainWindow

/-!
概要：指定した生成対象から次数一への射の像とその微分の像から初期窓を作る。
方針：可換四角形の像の射を微分に使い、像分解からその全射性を証明する。
規約：全体の複体の完全性は初期窓の構成自体に不要。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の小さい非輪状部分複体の始点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (A : ChainComplex C ℕ) (ψ : G ⟶ A.X 1)

/--
概要：指定した射とその微分の合成の可換四角形。
方針：生成対象上の恒等射と全体の微分を取る。
規約：像の関手性を使うための実際の四角形。
使われ方：Stacks 19.12.2、TT §3 の初期窓の微分。
-/
def initialImageChainSquare : Arrow.mk ψ ⟶ Arrow.mk (ψ ≫ A.d 1 0) :=
  Arrow.homMk (𝟙 G) (A.d 1 0) (by simp)

/--
概要：指定した射の像と微分の像を二項とする初期窓。
方針：像の射の可換性と像分解を用いる。
規約：左項は指定した生成対象の実際の商。
使われ方：Stacks 19.12.2、TT §3 の小さい部分複体の初期段階。
-/
def initialImageChainWindow : EmbeddedChainWindow A G 0 where
  left := image ψ
  right := image (ψ ≫ A.d 1 0)
  d := image.map (initialImageChainSquare A ψ)
  leftι := image.ι ψ
  rightι := image.ι (ψ ≫ A.d 1 0)
  left_mono := inferInstance
  right_mono := inferInstance
  comm := image.map_ι (initialImageChainSquare A ψ)
  cover := factorThruImage ψ
  cover_epi := inferInstance

/--
概要：初期窓の微分は全射。
方針：像分解の全射との合成が、微分の像への標準全射になることを使う。
規約：生成対象の projectivity を使わない。
使われ方：Stacks 19.12.2、TT §3 の最上位での完全性。
-/
instance initialImageChainWindow_d_epi : Epi (initialImageChainWindow A ψ).d := by
  have h : factorThruImage ψ ≫ (initialImageChainWindow A ψ).d =
      factorThruImage (ψ ≫ A.d 1 0) := by
    have hh := image.factor_map (initialImageChainSquare A ψ)
    change factorThruImage ψ ≫ (initialImageChainWindow A ψ).d =
      (𝟙 G) ≫ factorThruImage (ψ ≫ A.d 1 0) at hh
    rw [Category.id_comp] at hh
    exact hh
  have : Epi (factorThruImage ψ ≫ (initialImageChainWindow A ψ).d) := by
    rw [h]
    infer_instance
  exact epi_of_epi (factorThruImage ψ) _

end SerrePositivity.KST.DerivedGeometry
