module

public import SerrePositivity.KST.DerivedGeometry.ComplexProductHomotopy
public import SerrePositivity.KST.DerivedGeometry.ComplexDiagramTranspose
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
概要：完全な積の下で複体の積とコホモロジーを比較する。
方針：関手圏への転置と完全な極限関手のホモロジー比較を使う。
規約：積の完全性はここで明示し、全係数層には仮定しない。
使われ方：TT §3、Toën §3.2、Stacks 15.88.12・36.3.4 の加群値 Milnor 列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type w}
  (P : ι → CochainComplex C ℤ) [HasProductsOfShape ι C]

/--
概要：転置した複体のコホモロジー図式を各因子のコホモロジーと比較する。
方針：各評価関手の完全性によるホモロジー比較を束ねる。
規約：積の完全性はこの段階では不要。
使われ方：TT §3、Stacks 15.88 の積とコホモロジー。
-/
def productHomologyDiagramIso (n : ℤ) :
    (complexDiagramTranspose (.up ℤ) (Discrete.functor P)).homology n ≅
      Discrete.functor (fun a => (P a).homology n) :=
  Discrete.natIso (fun a =>
    ((complexDiagramTranspose (.up ℤ) (Discrete.functor P)).sc n).mapHomologyIso
      ((evaluation (Discrete ι) C).obj a) |>.symm)

/--
概要：完全な積は複体のコホモロジーと可換。
方針：転置した複体に完全な lim 関手を適用したホモロジー比較を使う。
規約：HasExactLimitsOfShape (Discrete ι) を明示する。
使われ方：TT §3、Toën §3.2、Stacks 36.3.4 の加群値 Milnor 列。
-/
def complexProductHomologyIso [HasExactLimitsOfShape (Discrete ι) C] (n : ℤ) :
    (complexProduct P).homology n ≅ ∏ᶜ (fun a => (P a).homology n) :=
  ((complexDiagramTranspose (.up ℤ) (Discrete.functor P)).sc n).mapHomologyIso
    (lim : (Discrete ι ⥤ C) ⥤ C) ≪≫
      (lim : (Discrete ι ⥤ C) ⥤ C).mapIso (productHomologyDiagramIso P n)

/--
概要：積のコホモロジー比較は各射影と両立する。
方針：lim から評価への射影自然変換のホモロジー比較を使う。
規約：抽象的な対象の同型だけでなく実際の射影の等式を与える。
使われ方：TT §3、Stacks 36.3.4 の差分射と Milnor 列。
-/
lemma complexProductHomologyIso_hom_π [HasExactLimitsOfShape (Discrete ι) C]
    (n : ℤ) (a : ι) :
    (complexProductHomologyIso P n).hom ≫ Pi.π (fun a => (P a).homology n) a =
      (HomologicalComplex.homologyFunctor C (.up ℤ) n).map (complexProductπ P a) := by
  let τ : (lim : (Discrete ι ⥤ C) ⥤ C) ⟶ (evaluation (Discrete ι) C).obj ⟨a⟩ :=
    { app F := limit.π F ⟨a⟩
      naturality F G f := limMap_π f ⟨a⟩ }
  have h := ShortComplex.homologyMap_mapNatTrans
    ((complexDiagramTranspose (.up ℤ) (Discrete.functor P)).sc n) τ
  change _ = ShortComplex.homologyMap
    (((complexDiagramTranspose (.up ℤ) (Discrete.functor P)).sc n).mapNatTrans τ)
  rw [h]
  simp only [complexProductHomologyIso, Iso.trans_hom, Category.assoc]
  change _ ≫ limMap (productHomologyDiagramIso P n).hom ≫ limit.π _ ⟨a⟩ = _
  rw [limMap_π]
  rfl

/--
概要：積の各コホモロジー射影はコホモロジーの積錐を与える。
方針：実際の射影と両立する比較同型で積の普遍性を移す。
規約：完全な積を持つ基礎圏について述べる。
使われ方：TT §3、Stacks 36.3.4 の差分射のコホモロジー計算。
-/
def complexProductHomologyIsLimit [HasExactLimitsOfShape (Discrete ι) C] (n : ℤ) :
    IsLimit (Fan.mk ((complexProduct P).homology n)
      (fun a => (HomologicalComplex.homologyFunctor C (.up ℤ) n).map
        (complexProductπ P a))) := by
  apply IsLimit.ofIsoLimit (productIsProduct (fun a => (P a).homology n))
  refine Cone.ext (complexProductHomologyIso P n).symm ?_
  intro ⟨a⟩
  change Pi.π (fun a => (P a).homology n) a =
    (complexProductHomologyIso P n).inv ≫
      (HomologicalComplex.homologyFunctor C (.up ℤ) n).map (complexProductπ P a)
  rw [← complexProductHomologyIso_hom_π]
  simp

end SerrePositivity.KST.DerivedGeometry
