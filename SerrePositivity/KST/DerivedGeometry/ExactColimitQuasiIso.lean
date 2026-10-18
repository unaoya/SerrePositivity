module

public import SerrePositivity.KST.DerivedGeometry.ExactColimitAcyclic
public import Mathlib.Algebra.Homology.Functor

/-!
概要：完全な余極限は複体の図式の成分ごとの準同型を準同型へ送る。
方針：図式の射を転置し、関手圏の評価による準同型判定と完全な colim を使う。
規約：複体の上下限を要求しない。
使われ方：Stacks Theorem 19.12.6、TT §3・§8、Toën §3.2 の極限順序数での準同型性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {J C : Type*} [Category* J] [Category* C] [Abelian C]
  {ι : Type*} (c : ComplexShape ι)

/--
概要：複体の図式の射を関手圏内の複体の射へ転置する。
方針：各次数の成分を評価して自然変換を作る。
規約：元の鎖写像の可換性を保持する。
使われ方：Stacks Theorem 19.12.6、TT §3 の超限遷移の比較。
-/
def complexDiagramTransposeMap {F G : J ⥤ HomologicalComplex C c} (f : F ⟶ G) :
    complexDiagramTranspose c F ⟶ complexDiagramTranspose c G where
  f i := Functor.whiskerRight f (HomologicalComplex.eval C c i)
  comm' i j hij := by ext k; exact (f.app k).comm i j

/--
概要：図式の転置と余極限の比較同型は図式の射に自然。
方針：各次数の評価の余極限保存の自然性を使う。
規約：同じ実際の余極限を比較する。
使われ方：Stacks Theorem 19.12.6、TT §3 の準同型の余極限保存。
-/
lemma colimitComplexTransposeIso_naturality [HasColimitsOfShape J C]
    {F G : J ⥤ HomologicalComplex C c} (f : F ⟶ G) :
    colim.map f ≫ (colimitComplexTransposeIso c G).hom =
      (colimitComplexTransposeIso c F).hom ≫
        ((colim : (J ⥤ C) ⥤ C).mapHomologicalComplex c).map (complexDiagramTransposeMap c f) := by
  ext n
  exact (preservesColimitNatIso (HomologicalComplex.eval C c n)).hom.naturality f

/--
概要：成分ごとに準同型な図式の射の転置は準同型。
方針：関手圏の評価による準同型の既存の判定を使う。
規約：すべての図式対象の実際の準同型性を入力する。
使われ方：Stacks Theorem 19.12.6、TT §3 の超限工程。
-/
lemma complexDiagramTransposeMap_quasiIso {F G : J ⥤ HomologicalComplex C c} (f : F ⟶ G)
    (h : ∀ j, QuasiIso (f.app j)) : QuasiIso (complexDiagramTransposeMap c f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
  intro j
  exact h j

/--
概要：完全な余極限は成分ごとの準同型を準同型へ送る。
方針：転置した射を完全な colim で写し、元の余極限の射へ比較同型で戻す。
規約：非有界複体に適用できる。
使われ方：Stacks Theorem 19.12.6、TT §3・§8、Toën §3.2 の非有界 K-injective 分解の極限工程。
-/
lemma quasiIso_colimMap_of_exactColimits [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    {F G : J ⥤ HomologicalComplex C c} (f : F ⟶ G) (h : ∀ j, QuasiIso (f.app j)) :
    QuasiIso (colim.map f) := by
  have : (colim : (J ⥤ C) ⥤ C).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : QuasiIso (complexDiagramTransposeMap c f) := complexDiagramTransposeMap_quasiIso c f h
  let e : Arrow.mk (colim.map f) ≅ Arrow.mk
      (((colim : (J ⥤ C) ⥤ C).mapHomologicalComplex c).map (complexDiagramTransposeMap c f)) :=
    Arrow.isoMk (colimitComplexTransposeIso c F) (colimitComplexTransposeIso c G)
      (colimitComplexTransposeIso_naturality c f).symm
  exact ((HomologicalComplex.quasiIso C c).arrow_iso_iff e).mpr (show
    QuasiIso (((colim : (J ⥤ C) ⥤ C).mapHomologicalComplex c).map
      (complexDiagramTransposeMap c f)) from
        HomologicalComplex.quasiIso_map_of_preservesHomology
          (complexDiagramTransposeMap c f) (colim : (J ⥤ C) ⥤ C))

end SerrePositivity.KST.DerivedGeometry
