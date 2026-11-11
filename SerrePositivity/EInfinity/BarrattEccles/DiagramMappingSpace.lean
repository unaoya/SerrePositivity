module

public import SerrePositivity.EInfinity.BarrattEccles.DiagramModel
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero

/-!
# E 代数図式の具体的な関手的導来写像空間

概要：BM 命題 4.1・Hovey §5 の射影図式モデルから Kan な Map^h を構成する。
方針：図式の生成類の実際の関手的分解で始域 frame を選ぶ。
規約：全図式の fibrancy を証明して用い、単体集合モデルは仮定しない。
使われ方：定値図式からの導来 Hom と重み付き錐の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.Diagram

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：図式モデルの cofibrant 側の関手的分解（BM §1、Hovey §5）。
方針：自由な図式生成類の小対象分解を使う。
規約：モデル構造と分解の存在は具体的に証明して供給する。
使われ方：図式の余単体的始域 resolution。 -/
def mappingCofibrantFactorization :
    let := projectiveModelCategory A K
    MorphismProperty.FunctorialFactorizationData
      (cofibrations (K ⥤ (operad A).Algebra)) (trivialFibrations (K ⥤ (operad A).Algebra)) := by
  let := projectiveModelCategory A K
  have := cofibrantlyGenerated A K
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
    (generatingCofibrations A K) (generatingTrivialCofibrations A K)
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：任意の二つの E 代数図式の実際の Map^h（Hovey §5）。
方針：図式の選んだ cofibrant frame の Hom を取る。
規約：終域図式はすべて fibrant なので元の図式をそのまま使う。
使われ方：一般 homotopy 極限の図式の導来 Hom の比較。 -/
def mappingSpace : (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ (K ⥤ (operad A).Algebra) ⥤ SSet.{u} := by
  let := projectiveModelCategory A K
  exact (cosimplicialResolutionFamily (mappingCofibrantFactorization A K)).obj.op ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

/-- 概要：図式の導来写像空間は全次元で Kan（Hovey §5）。
方針：図式の Reedy cofibrant 始域 frame と全終域の fibrancy を使う。
規約：元の両図式に置換条件の入力はない。
使われ方：定値図式の具体的な frame Hom の比較。 -/
lemma mappingSpace_kanComplex (F : (K ⥤ (operad A).Algebra)ᵒᵖ)
    (G : K ⥤ (operad A).Algebra) : SSet.KanComplex (((mappingSpace A K).obj F).obj G) := by
  let := projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A K)
  have := isFibrant A K G
  exact cosimplicialHom_kanComplex _ (q.cofibrant F.unop)
    (q.atObject F.unop).homotopicallyConstant G

/-- 概要：図式の Map^h の π₀ は元の図式の局所化後の Hom（Hovey §5）。
方針：実際の始域 resolution の π₀ 比較を使う。
規約：具体的な射影図式モデルの普通の局所化を取る。
使われ方：一般 homotopy 極限の定値図式との導来随伴の Hom 比較。 -/
def mappingSpacePiZeroEquiv (F : (K ⥤ (operad A).Algebra)ᵒᵖ)
    (G : K ⥤ (operad A).Algebra) :
    let := projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    SSet.π₀ (((mappingSpace A K).obj F).obj G) ≃ (Q.obj F.unop ⟶ Q.obj G) := by
  let := projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A K)
  have := isFibrant A K G
  exact resolutionPiZeroLocalizationEquiv Q (q.atObject F.unop) G

end SerrePositivity.EInfinity.BarrattEccles.Diagram
