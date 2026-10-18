module

public import SerrePositivity.KST.DerivedGeometry.AdjacentBiproductContraction

/-!
概要：任意の非有界複体へ contractible 複体から各項分裂全射を構成する。
方針：一つ前の次数と現在の次数の双積から、微分と恒等写像の和で射を作る。
規約：injective 性を仮定しない。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の準同型拡大の pullback 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] (Q : CochainComplex C ℤ)

/--
概要：任意の複体の一つ前の次数から作る contractible な隣接双積複体。
方針：既証の隣接双積複体の対象族をずらす。
規約：整数添字。
使われ方：Stacks Lemma 19.12.5、TT §3 の準同型拡大。
-/
def contractibleEpiSource : CochainComplex C ℤ :=
  adjacentBiproductComplex (fun n => Q.X (n - 1))

/--
概要：contractible な複体から元の複体への全射の鎖写像。
方針：第一成分の微分と第二成分の恒等を合成する。
規約：元の微分の二乗が零であることから鎖写像を得る。
使われ方：Stacks Lemma 19.12.5、TT §3 の余核複体への contractible 全射。
-/
def contractibleEpi : contractibleEpiSource Q ⟶ Q where
  f n := biprod.desc (Q.d (n - 1) n)
    (eqToHom (congrArg Q.X (show (n + 1) - 1 = n by omega)))
  comm' i j hij := by
    have h : i + 1 = j := hij
    subst j
    dsimp [contractibleEpiSource, adjacentBiproductComplex]
    apply biprod.hom_ext' <;> simp [Category.assoc]

/--
概要：contractible 全射の各次数の切断。
方針：第二成分の包含を添字の比較と合成する。
規約：鎖写像であることは要求しない。
使われ方：Stacks Lemma 19.12.5、TT §3 の各項の部分対象。
-/
def contractibleEpiSection (n : ℤ) : Q.X n ⟶ (contractibleEpiSource Q).X n :=
  eqToHom (congrArg Q.X (show n = (n + 1) - 1 by omega)) ≫ biprod.inr

/--
概要：各次数の切断と全射の合成は恒等。
方針：双積の射影公式と添字の同型の逆性を使う。
規約：実際の成分の等式。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の injective 因子化。
-/
lemma contractibleEpiSection_comp (n : ℤ) :
    contractibleEpiSection Q n ≫ (contractibleEpi Q).f n = 𝟙 _ := by
  simp [contractibleEpiSection, contractibleEpi, Category.assoc]

/--
概要：contractible 全射は各次数で全射。
方針：第二成分の包含と添字の比較の逆を用いて右逆を作る。
規約：右逆は鎖写像とは主張しない。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の各項での injective 因子化。
-/
instance contractibleEpi_f_epi (n : ℤ) : Epi ((contractibleEpi Q).f n) := by
  have h : (eqToHom (congrArg Q.X (show n = (n + 1) - 1 by omega)) ≫ biprod.inr) ≫
      (contractibleEpi Q).f n = 𝟙 _ := by simp [contractibleEpi, Category.assoc]
  exact epi_of_epi_fac h

/--
概要：contractible な全射は複体の圏でも全射。
方針：各項での全射性を使う。
規約：非有界複体。
使われ方：Stacks Lemma 19.12.5、TT §3 の pullback の短完全列。
-/
instance contractibleEpi_epi : Epi (contractibleEpi Q) :=
  HomologicalComplex.epi_of_epi_f _ (fun _ => inferInstance)

/--
概要：contractible な全射の始域は非輪状。
方針：構成済みの縮約の結果を適用する。
規約：元の Q の非輪状性は不要。
使われ方：Stacks Lemma 19.12.5、TT §3 の準同型性の判定。
-/
lemma contractibleEpiSource_acyclic : (contractibleEpiSource Q).Acyclic :=
  adjacentBiproductComplex_acyclic _

end SerrePositivity.KST.DerivedGeometry
