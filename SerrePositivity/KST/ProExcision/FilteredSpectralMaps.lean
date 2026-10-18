module

public import SerrePositivity.KST.ProExcision.SpectralObjectMaps

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 濾過の自然変換とスペクトル対象の射

概要：濾過間の自然変換を、連結写像と可換なスペクトル対象の射へ持ち上げる。
方針：合成可能図式への自然変換と元のスペクトル対象の δ の自然性を使う。
規約：各区間の標準比較同型を省略しない。
使われ方：KST Lemma 4.10 の Koszul 冪遷移に対する頁の自然性。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits ComposableArrows

variable {A : Type u} [Category A] {B : Type v} [Category B]
variable {D : Type w} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

/-- 概要：指数関手の自然変換に沿って引き戻したスペクトル対象の間の射。
方針：区間図式の自然変換を評価し、三段図式上の δ の自然性を標準比較で移す。
規約：同じ元のスペクトル対象を二つの関手に沿って引き戻す。
使われ方：KST Lemma 4.10 の濾過間の射から実際の頁の射を得る。 -/
def spectralPrecompMap (X : Triangulated.SpectralObject D B)
    {F G : A ⥤ B} (α : F ⟶ G) : X.precomp F ⟶ X.precomp G where
  hom := Functor.whiskerRight (composableArrowsMapNatTrans α 1) X.ω₁
  comm f g := by
    let T := mk₂ f g
    let af := (composableArrowsMapNatTrans α 1).app (mk₁ f)
    let ag := (composableArrowsMapNatTrans α 1).app (mk₁ g)
    let a₂ := (composableArrowsMapNatTrans α 2).app T
    let a₀₁ := (functorArrows B 0 1 2).map a₂
    let a₁₂ := (functorArrows B 1 2 2).map a₂
    have hf' : (F.mapComposableArrowsObjMk₁Iso f).inv ≫ af =
        a₀₁ ≫ (G.mapComposableArrowsObjMk₁Iso f).inv := by
      ext <;>
        simp [af, a₀₁, a₂, T, composableArrowsMapNatTrans,
          Functor.mapComposableArrowsObjMk₁Iso, ComposableArrows.isoMk₁]
    have hg' : ag ≫ (G.mapComposableArrowsObjMk₁Iso g).hom =
        (F.mapComposableArrowsObjMk₁Iso g).hom ≫ a₁₂ := by
      ext <;>
        simp [ag, a₁₂, a₂, T, composableArrowsMapNatTrans,
          Functor.mapComposableArrowsObjMk₁Iso, ComposableArrows.isoMk₁]
    let uF := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso g).hom
    let uG := X.ω₁.map (G.mapComposableArrowsObjMk₁Iso g).hom
    let vF := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso f).inv
    let vG := X.ω₁.map (G.mapComposableArrowsObjMk₁Iso f).inv
    let mf := X.ω₁.map af
    let mg := X.ω₁.map ag
    let cf := X.ω₁.map a₀₁
    let cg := X.ω₁.map a₁₂
    let dF := X.δ'.app ((F.mapComposableArrows 2).obj T)
    let dG := X.δ'.app ((G.mapComposableArrows 2).obj T)
    have hf : vF ≫ mf = cf ≫ vG := by
      change X.ω₁.map _ ≫ X.ω₁.map _ = X.ω₁.map _ ≫ X.ω₁.map _
      rw [← X.ω₁.map_comp, ← X.ω₁.map_comp, hf']
    have hg : mg ≫ uG = uF ≫ cg := by
      change X.ω₁.map _ ≫ X.ω₁.map _ = X.ω₁.map _ ≫ X.ω₁.map _
      rw [← X.ω₁.map_comp, ← X.ω₁.map_comp, hg']
    have hδ : cg ≫ dG = dF ≫ cf⟦(1 : ℤ)⟧' := X.δ'.naturality a₂
    change (uF ≫ dF ≫ vF⟦(1 : ℤ)⟧') ≫ mf⟦(1 : ℤ)⟧' =
      mg ≫ (uG ≫ dG ≫ vG⟦(1 : ℤ)⟧')
    calc
      _ = uF ≫ dF ≫ (vF⟦(1 : ℤ)⟧' ≫ mf⟦(1 : ℤ)⟧') := by simp only [Category.assoc]
      _ = uF ≫ dF ≫ (vF ≫ mf)⟦(1 : ℤ)⟧' :=
        congrArg (fun f ↦ uF ≫ dF ≫ f) ((shiftFunctor D (1 : ℤ)).map_comp vF mf).symm
      _ = uF ≫ dF ≫ (cf ≫ vG)⟦(1 : ℤ)⟧' :=
        congrArg (fun f ↦ uF ≫ dF ≫ (shiftFunctor D (1 : ℤ)).map f) hf
      _ = uF ≫ (dF ≫ cf⟦(1 : ℤ)⟧') ≫ vG⟦(1 : ℤ)⟧' := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
      _ = uF ≫ (cg ≫ dG) ≫ vG⟦(1 : ℤ)⟧' :=
        congrArg (fun f ↦ uF ≫ f ≫ vG⟦(1 : ℤ)⟧') hδ.symm
      _ = (uF ≫ cg) ≫ dG ≫ vG⟦(1 : ℤ)⟧' := by simp only [Category.assoc]
      _ = (mg ≫ uG) ≫ dG ≫ vG⟦(1 : ℤ)⟧' :=
        congrArg (fun f ↦ f ≫ dG ≫ vG⟦(1 : ℤ)⟧') hg.symm
      _ = _ := by simp only [Category.assoc]

/-- 概要：指数関手の恒等自然変換はスペクトル対象の恒等射へ移る。
方針：区間ごとの自然変換を比較して元の区間関手の恒等保存を使う。
規約：連結写像との可換性の証明は射の等式に影響しない。
使われ方：KST Lemma 4.10 の濾過の塔の恒等遷移。 -/
theorem spectralPrecompMap_id (X : Triangulated.SpectralObject D B) (F : A ⥤ B) :
    spectralPrecompMap X (𝟙 F) = 𝟙 (X.precomp F) := by
  apply Triangulated.SpectralObject.hom_ext
  change Functor.whiskerRight (composableArrowsMapNatTrans (𝟙 F) 1) X.ω₁ = 𝟙 _
  rw [composableArrowsMapNatTrans_id]
  ext T
  exact X.ω₁.map_id _

/-- 概要：指数関手の自然変換の合成はスペクトル対象の射の合成へ移る。
方針：合成可能図式への持ち上げの合成保存と元の区間関手の合成保存を使う。
規約：合成の順序を固定する。使われ方：KST Lemma 4.10 の塔の遷移合成則。 -/
theorem spectralPrecompMap_comp (X : Triangulated.SpectralObject D B)
    {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) :
    spectralPrecompMap X (α ≫ β) = spectralPrecompMap X α ≫ spectralPrecompMap X β := by
  apply Triangulated.SpectralObject.hom_ext
  change Functor.whiskerRight (composableArrowsMapNatTrans (α ≫ β) 1) X.ω₁ =
    Functor.whiskerRight (composableArrowsMapNatTrans α 1) X.ω₁ ≫
      Functor.whiskerRight (composableArrowsMapNatTrans β 1) X.ω₁
  rw [composableArrowsMapNatTrans_comp]
  ext T
  exact X.ω₁.map_comp _ _

/-- 概要：スペクトル対象への引き戻しを指数関手の圏からの関手として構成する。
方針：自然変換を連結写像と可換な射へ持ち上げ、恒等・合成保存を使う。
規約：元のスペクトル対象を固定する。使われ方：KST Lemma 4.10 の濾過の塔の持ち上げ。 -/
def spectralPrecompFunctor (X : Triangulated.SpectralObject D B) :
    (A ⥤ B) ⥤ Triangulated.SpectralObject D A where
  obj F := X.precomp F
  map α := spectralPrecompMap X α
  map_id F := spectralPrecompMap_id X F
  map_comp α β := spectralPrecompMap_comp X α β

variable {R : Type u} [CommRing R]

/-- 概要：複体の濾過からホモロジースペクトル対象を得る実際の関手。
方針：mapping cone スペクトル対象への引き戻し関手に、ホモロジー関手の作用を合成する。
規約：既存 filteredHomologySpectralObject と同じ対象を持つ。
使われ方：KST Lemma 4.10 の実際の濾過間の射と頁の塔。 -/
def filteredHomologySpectralFunctor (I : Type v) [Category I] :
    (I ⥤ CochainComplex (ModuleCat.{u} R) ℤ) ⥤ Abelian.SpectralObject (ModuleCat.{u} R) I :=
  spectralPrecompFunctor (HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} R)) ⋙
    Triangulated.SpectralObject.mapHomologicalFunctorFunctor
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0) I

end SerrePositivity.KST.ProExcision
