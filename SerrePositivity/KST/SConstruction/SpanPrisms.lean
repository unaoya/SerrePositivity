module
public import SerrePositivity.KST.SConstruction.McCarthyLambdaNu
public import SerrePositivity.KST.SConstruction.McCarthyLambdaMu

/-! # 共通始点を持つ二つの prism の span への貼り合わせ
概要：任意のパラメーター上で始点が等しい二本の枝を標準 span に貼る。
方針：ホーンの pushout をパラメーターとの積に送る。
規約：二本の枝の制限を厳密に保持する。使われ方：McCarthy の押し出しの入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：二枝の共通始点の包含は始点 prism の制限として表せる。
方針：区間の零頂点への定値射を使う。
規約：パラメーターは任意。使われ方：二枝の貼り合わせ条件。 -/
lemma spanPrism_source (K : SSet.{u}) :
    stdSimplex.δ (1 : Fin 2) ▷ K = snd (Δ[0] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := by
  rw [stdSimplex.δ_one_eq_const]
  rfl

/-- 概要：区間の二枝の pushout は任意のパラメーターとの積で保たれる。
方針：tensorRight は左随伴なので pushout を保つ。
規約：二枝の順序は 01、02。使われ方：prism の族の降下。 -/
lemma spanPrisms_isPushout (K : SSet.{u}) :
    IsPushout (stdSimplex.δ (1 : Fin 2) ▷ K) (stdSimplex.δ (1 : Fin 2) ▷ K)
      (horn₂₀.ι₀₁ ▷ K) (horn₂₀.ι₀₂ ▷ K) := horn₂₀.isPushout.map (tensorRight K)

/-- 概要：共通始点を持つ二つの prism を span の族に貼る。
方針：パラメーターとの積を取った pushout の普遍性。
規約：第一枝は上辺、第二枝は左辺。使われ方：McCarthy の λ→μ と λ→ν の貼り合わせ。 -/
def spanPrisms {K D : SSet.{u}} (L R : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R) :
    (horn 2 0 : SSet.{u}) ⊗ K ⟶ D :=
  (spanPrisms_isPushout K).desc L R (by simp only [spanPrism_source, Category.assoc, h])

/-- 概要：貼り合わせた span の第一枝は指定した L。
方針：pushout の第一制限の式。
規約：全単体で厳密な等号。使われ方：ρ の上辺の回収。 -/
lemma spanPrisms_left {K D : SSet.{u}} (L R : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R) :
    (horn₂₀.ι₀₁ ▷ K) ≫ spanPrisms L R h = L := (spanPrisms_isPushout K).inl_desc _ _ _

/-- 概要：貼り合わせた span の第二枝は指定した R。
方針：pushout の第二制限の式。
規約：全単体で厳密な等号。使われ方：ρ の左辺の回収。 -/
lemma spanPrisms_right {K D : SSet.{u}} (L R : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R) :
    (horn₂₀.ι₀₂ ▷ K) ≫ spanPrisms L R h = R := (spanPrisms_isPushout K).inr_desc _ _ _

/-- 概要：span の族の二つの射は二枝への制限で等号を判定できる。
方針：積を取った pushout の射の外延性。
規約：標的の仮定は不要。使われ方：添字と後合成への自然性。 -/
lemma spanPrisms_hom_ext {K D : SSet.{u}} {F G : (horn 2 0 : SSet.{u}) ⊗ K ⟶ D}
    (h₁ : (horn₂₀.ι₀₁ ▷ K) ≫ F = (horn₂₀.ι₀₁ ▷ K) ≫ G)
    (h₂ : (horn₂₀.ι₀₂ ▷ K) ≫ F = (horn₂₀.ι₀₂ ▷ K) ≫ G) : F = G :=
  (spanPrisms_isPushout K).hom_ext h₁ h₂

/-- 概要：二枝の貼り合わせは標的への後合成と可換。
方針：二枝に制限して同じ射となることを確認する。
規約：貼り合わせ条件の証明の選択に依存しない。使われ方：cofiber 図式を C の正方形へ移す。 -/
lemma spanPrisms_post {K D E : SSet.{u}} (L R : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R) (q : D ⟶ E)
    (h' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (L ≫ q) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (R ≫ q)) :
    spanPrisms L R h ≫ q = spanPrisms (L ≫ q) (R ≫ q) h' := by
  apply spanPrisms_hom_ext
  · rw [← Category.assoc, spanPrisms_left, spanPrisms_left]
  · rw [← Category.assoc, spanPrisms_right, spanPrisms_right]

/-- 概要：二枝の貼り合わせはパラメーターの引き戻しと可換。
方針：二枝で tensor の交換則と制限の式を使う。
規約：任意の i に対する厳密な等号。使われ方：McCarthy の span の面・退化の自然性。 -/
lemma spanPrisms_pre {K K' D : SSet.{u}} (L R : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R) (i : K' ⟶ K)
    (h' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K' ≫ ((Δ[1] ◁ i) ≫ L) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K' ≫ ((Δ[1] ◁ i) ≫ R)) :
    ((horn 2 0 : SSet.{u}) ◁ i) ≫ spanPrisms L R h =
      spanPrisms ((Δ[1] ◁ i) ≫ L) ((Δ[1] ◁ i) ≫ R) h' := by
  apply spanPrisms_hom_ext
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc, spanPrisms_left, spanPrisms_left]
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc, spanPrisms_right, spanPrisms_right]

/-- 概要：第一枝が共通始点で一定なら貼り合わせは左辺を標準形状で引き戻した span。
方針：二枝に制限し、恒等枝の標準形状の式を使う。
規約：prism 全体の厳密な等号。使われ方：ρ の時刻零の正規化。 -/
lemma spanPrisms_constant_left {K D : SSet.{u}} (L R : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R) (f : K ⟶ D)
    (hL : L = snd (Δ[1] : SSet.{u}) K ≫ f) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R = f) :
    spanPrisms L R h = (identitySpanShape false ▷ K) ≫ R := by
  have h₀ : horn₂₀.ι₀₁ ≫ identitySpanShape false =
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : (Δ[1] : SSet.{u}) ⟶ Δ[1]) := by
    rw [identitySpanShape, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    apply SSet.yonedaEquiv.injective
    decide
  have h₁ : horn₂₀.ι₀₂ ≫ identitySpanShape false = 𝟙 (Δ[1] : SSet.{u}) :=
    identitySpanSection_shape false
  apply spanPrisms_hom_ext
  · rw [spanPrisms_left, ← Category.assoc, ← comp_whiskerRight, h₀]
    have he : (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
        (Δ[1] : SSet.{u}) ⟶ Δ[1]) ▷ K = snd (Δ[1] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := rfl
    rw [he, Category.assoc, hR, hL]
  · rw [spanPrisms_right, ← Category.assoc, ← comp_whiskerRight, h₁]
    simp

end SerrePositivity.KST.SConstruction
