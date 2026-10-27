module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeFullSquare
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices
public import SerrePositivity.KST.LocalizingInvariants.CofiberRelativeDiagramComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleStability

/-!
概要：元 dg cone 全族を Sp 正本の cofiber 図式空間へ入れ、同じ底辺の選択図式へ全比較する。
方針：元全四角形の二変数を交換し、点ごとの元 cone 回収で full subcomplex に入れる。
規約：元両二胞体と元零角を保持。cofiber API は Sp の正本を使用する。
使われ方：元実逆回転と固定 ν の全図式比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories DGNerve
open LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (D P : Type (u + 1))
  [DGCategory R D] [Small.{u} D] [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (RightModule R D)) (η : StrictNatTrans F G)
local notation "X" => dgNerve R (RightModule R D)
/-- 概要：元全 cone 四角形を元パラメータ上の全四角形族へ交換する。
方針：同じ内部 Hom 交換を使う。規約：元全単体を保持。
使われ方：Sp 正本の cofiber 空間への持ち上げ。 -/
def dgModuleNaturalConeSquareFamily : dgNerve R P ⟶
    (ihom (Δ[1] ⊗ Δ[1] : SSet.{u + 1})).obj (X) :=
  internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1] : SSet.{u + 1})
    (dgNerve R P) (X) (dgModuleNaturalConeFullSquare R D P F G η)
local notation "H" => dgModuleNaturalConeSquareFamily R D P F G η

/-- 概要：元 dg cone の同じ全四角形族を Sp 正本の cofiber 空間へ入れる。
方針：交換した全族の各頂点で元実 cone の零角・押し出しを厳密回収する。
規約：元両二胞体を変更しない。使われ方：同じ底辺の選択 cofiber との全比較。 -/
def dgModuleNaturalConeCofiberFamily : dgNerve R P ⟶ CofiberDiagrams.space (X) :=
  fullSubcomplexLift CofiberDiagrams.Predicate (H) (by
    intro k
    obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective k
    have hf := internalHomFlipHomEquiv_app_zero (dgModuleNaturalConeFullSquare R D P F G η)
      (Simplex.vertex x)
    have hs := (congrArg squareDiagram hf).trans
      (squareDiagram_functorVertex (dgModuleNaturalConeFullSquare R D P F G η ≫
        evaluateFunctorAt (Y := (X)) (Simplex.vertex x)))
    have he := hs.trans (dgModuleNaturalConeFullSquare_evaluation R D P F G η x)
    exact (congrArg (fun sq => IsZeroVertex (squareVertex sq 0 1) ∧ IsPushoutSquare sq) he).mpr
      ⟨(dgModuleConeZeroTriangle R D (dgModuleNaturalConeArrow R D F G η x)).zero_corner,
        dgModuleConeSquare_isPushout R D _⟩)

/-- 概要：元 cofiber 空間への持ち上げは元全四角形の交換族を厳密回収する。
方針：同じ full subcomplex 持ち上げの包含則を使う。
規約：全単体の等号。使われ方：元指定二胞体の回収。 -/
lemma dgModuleNaturalConeCofiberFamily_inclusion :
    dgModuleNaturalConeCofiberFamily R D P F G η ≫ CofiberDiagrams.inclusion (X) = (H) :=
  fullSubcomplexLift_ι _ _ _

/-- 概要：同じ元 cofiber 全族の底辺を全矢印族として保持する。
方針：Sp 正本の底辺評価を同じ元族へ合成する。
規約：元底辺を選び直さない。使われ方：同じ底辺を持つ選択 cofiber の入力。 -/
def dgModuleNaturalConeCofiberBottom :
    dgNerve R P ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj (X) :=
  dgModuleNaturalConeCofiberFamily R D P F G η ≫ CofiberDiagrams.bottom (X)

/-- 概要：元 cofiber 全族と同じ底辺の選択全族との比較を図式空間内に保持する。
方針：Sp 正本の同じ底辺の相対比較を使う。
規約：元底辺の射影は指定恒等。使われ方：元指定境界を保つ全比較。 -/
def dgModuleNaturalConeCofiberLiftComparison : FunctorIso
    (dgModuleNaturalConeCofiberFamily R D P F G η)
    (CofiberDiagrams.lift (X) (dgModuleNaturalConeCofiberBottom R D P F G η)) :=
  CofiberDiagrams.relativeComparison (X)
    (dgModuleNaturalConeCofiberFamily R D P F G η)
    (CofiberDiagrams.lift (X) (dgModuleNaturalConeCofiberBottom R D P F G η))
    (CofiberDiagrams.lift_bottom (X) (dgModuleNaturalConeCofiberBottom R D P F G η)).symm

/-- 概要：同じ元全比較の底辺射影は全関手圏の指定恒等そのもの。
方針：Sp 正本の相対比較の射影回収を直接使う。
規約：点ごとの恒等性へ弱めない。使われ方：元底辺の指定境界の保存。 -/
lemma dgModuleNaturalConeCofiberLiftComparison_bottom :
    Arrow.mk (FunctorIso.postcomp
      (dgModuleNaturalConeCofiberLiftComparison R D P F G η) (CofiberDiagrams.bottom (X))).hom =
    Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
      (CofiberDiagrams.lift (X) (dgModuleNaturalConeCofiberBottom R D P F G η) ≫
        CofiberDiagrams.bottom (X))) :
      hoFunctor.obj ((ihom (dgNerve R P)).obj ((ihom (Δ[1] : SSet.{u + 1})).obj (X))))) :=
  CofiberDiagrams.relativeComparison_bottom_arrow (X)
    (dgModuleNaturalConeCofiberFamily R D P F G η)
    (CofiberDiagrams.lift (X) (dgModuleNaturalConeCofiberBottom R D P F G η))
    (CofiberDiagrams.lift_bottom (X) (dgModuleNaturalConeCofiberBottom R D P F G η)).symm

/-- 概要：元全 cofiber 図式と同じ底辺を持つ選択図式との全関手同型。
方針：Sp 正本の底辺を保つ相対全図式比較をそのまま使う。
規約：元底辺を厳密保持し、終点同型だけで代用しない。
使われ方：元実逆回転の全 cofiber 図式比較。 -/
def dgModuleNaturalConeCofiberFamilyComparison : FunctorIso
    (dgModuleNaturalConeCofiberFamily R D P F G η ≫ CofiberDiagrams.inclusion (X))
    (CofiberDiagrams.lift (X) (dgModuleNaturalConeCofiberBottom R D P F G η) ≫
      CofiberDiagrams.inclusion (X)) :=
  FunctorIso.postcomp (dgModuleNaturalConeCofiberLiftComparison R D P F G η)
    (CofiberDiagrams.inclusion (X))

end SerrePositivity.KST.SConstruction
