module
public import SerrePositivity.KST.SConstruction.ExactMaps
public import SerrePositivity.KST.SConstruction.CoreSimplicial

/-! # S 構成の後合成と単体構造との自然性
概要：零対象と押し出しを保つ射は S• とその core の間の自然な写像を誘導する。
方針：内部 Hom の後合成を gapped の全部分複体へ持ち上げる。
規約：BGT §7。恒等・合成・面退化の自然性は厳密な等号。
使われ方：反復 S 構成と dg 関手への適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対象と押し出しを保つ射が S_n の間に誘導する写像。
方針：内部 Hom の後合成を頂点ごとの gapped 条件で持ち上げる。
規約：全ての図式の選択を保つ。使われ方：S 構成の射への作用。 -/
def sPostcomp (n : ℕ) {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    sConstruction n C ⟶ sConstruction n D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((gappedSubcomplex n C).ι ≫ (ihom (arNerve n)).map f) (by
    intro v
    let F := gappedDiagram v
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D).symm
      (((ihom (arNerve n)).map f).app (Opposite.op ⦋0⦌) v.val))
    rw [← hv]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ f)))
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) D (F ≫ f)))
    rw [Equiv.symm_apply_apply]
    exact (gappedDiagram_isGapped v).postcomp f hf)

/-- 概要：S_n の後合成を含めると通常の内部 Hom の後合成。
方針：全部分複体への持ち上げの包含後の式。
規約：全単体での等号。使われ方：関手法則の比較。 -/
lemma sPostcomp_ι (n : ℕ) {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    sPostcomp n f hf ≫ (gappedSubcomplex n D).ι =
      (gappedSubcomplex n C).ι ≫ (ihom (arNerve n)).map f := rfl

/-- 概要：恒等射による S_n の後合成は恒等射。
方針：全部分複体への単射の後で内部 Hom の恒等法則を使う。
規約：厳密等号。使われ方：S 構成の関手性。 -/
lemma sPostcomp_id (n : ℕ) (C : SSet.{u}) :
    sPostcomp n (𝟙 C) (preservesSConstructionData_id C) = 𝟙 (sConstruction n C) := by
  apply (cancel_mono (gappedSubcomplex n C).ι).1
  erw [sPostcomp_ι, CategoryTheory.Functor.map_id]

/-- 概要：二つの射の合成による S_n の後合成は二つの後合成写像の合成。
方針：包含後で内部 Hom の合成法則を使う。
規約：保存条件の証明の選択は proof irrelevance で一致する。
使われ方：S 構成の関手性。 -/
lemma sPostcomp_comp (n : ℕ) {C D E : SSet.{u}} (f : C ⟶ D) (g : D ⟶ E)
    (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g) :
    sPostcomp n (f ≫ g) (hf.comp hg) = sPostcomp n f hf ≫ sPostcomp n g hg := by
  apply (cancel_mono (gappedSubcomplex n E).ι).1
  rw [sPostcomp_ι, CategoryTheory.Functor.map_comp, Category.assoc, sPostcomp_ι]
  simp only [← Category.assoc]
  erw [sPostcomp_ι]

/-- 概要：S_n の後合成は単体作用と可換。
方針：包含後で内部 Hom の前合成と後合成の自然性を使う。
規約：全ての面・退化の厳密な可換性。使われ方：単体的 S• の射。 -/
lemma sPostcomp_sMap {m n : ℕ} {C D : SSet.{u}} (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (θ : Fin (m + 1) →o Fin (n + 1)) :
    sPostcomp n f hf ≫ sMap D θ = sMap C θ ≫ sPostcomp m f hf := by
  apply (cancel_mono (gappedSubcomplex m D).ι).1
  rw [Category.assoc, sMap_ι, ← Category.assoc, sPostcomp_ι,
    Category.assoc, (pre (arNerveMap θ)).naturality]
  symm
  rw [Category.assoc, sPostcomp_ι, ← Category.assoc, sMap_ι, Category.assoc]

/-- 概要：零対象と押し出しを保つ射は単体的 S 構成の自然変換を誘導する。
方針：各段の後合成写像と単体作用との可換性を束ねる。
規約：始域と終域の安定性は不要。使われ方：反復 S• の関手性の準備。 -/
def simplicialSPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    simplicialSConstruction C ⟶ simplicialSConstruction D where
  app n := sPostcomp n.unop.len f hf
  naturality {_d _e} θ := (sPostcomp_sMap f hf θ.unop.toOrderHom).symm

/-- 概要：S• の後合成を各段の core へ送る。
方針：α2 の core 関手で自然変換を後合成する。
規約：可逆な辺の保存は core 関手が担う。使われ方：K 空間の射への作用の基礎。 -/
def simplicialCoreSPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    simplicialCoreSConstruction C ⟶ simplicialCoreSConstruction D :=
  Functor.whiskerRight (simplicialSPostcomp f hf) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：S• の後合成が対角実現の間に誘導する写像。
方針：二重単体集合の自然変換を対角で制限する。
規約：基点の選択はまだ課さない。使われ方：K 理論の関手性と反復実現。 -/
def diagonalSPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    diagonalCoreSConstruction C ⟶ diagonalCoreSConstruction D :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.map (simplicialCoreSPostcomp f hf))

/-- 概要：S_n の後合成は零図式を像の零図式へ厳密に送る。
方針：包含後で定値図式の後合成の式を使う。
規約：像の零頂点を使い、既定の零対象との等号は仮定しない。
使われ方：反復構成の基点と零対象比較。 -/
lemma sPostcomp_zeroVertex (n : ℕ) {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    (sPostcomp n f hf).app (Opposite.op ⦋0⦌) (sConstructionZeroVertex n z hz) =
      sConstructionZeroVertex n (f.app (Opposite.op ⦋0⦌) z) (hf.1 z hz) := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.const z : arNerve n ⟶ C) ≫ f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (f.app (Opposite.op ⦋0⦌) z) : arNerve n ⟶ D)
  rw [SSet.const_comp]

/-- 概要：対角実現の後合成は恒等射を保つ。
方針：各次数で S_n と core 関手の恒等法則を使う。
規約：厳密等号。使われ方：K 理論の射の恒等法則。 -/
lemma diagonalSPostcomp_id (C : SSet.{u}) :
    diagonalSPostcomp (𝟙 C) (preservesSConstructionData_id C) = 𝟙 (diagonalCoreSConstruction C) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
    (sPostcomp d.unop.len (𝟙 C) (preservesSConstructionData_id C))).app d x = x
  rw [sPostcomp_id]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (𝟙 (sConstruction d.unop.len C))).app d x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- 概要：対角実現の後合成は射の合成を保つ。
方針：各次数で S_n と core 関手の合成法則を使う。
規約：厳密等号。使われ方：K 理論の射の合成法則。 -/
lemma diagonalSPostcomp_comp {C D E : SSet.{u}} (f : C ⟶ D) (g : D ⟶ E)
    (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g) :
    diagonalSPostcomp (f ≫ g) (hf.comp hg) = diagonalSPostcomp f hf ≫ diagonalSPostcomp g hg := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcomp d.unop.len (f ≫ g) (hf.comp hg))).app d x =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcomp d.unop.len g hg)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcomp d.unop.len f hf)).app d x)
  rw [sPostcomp_comp]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp (sPostcomp d.unop.len f hf) (sPostcomp d.unop.len g hg)) d) x

/-- 概要：対角の後合成は零図式の頂点をその像の零図式に送る。
方針：core の包含後で S_0 の零図式の後合成を使う。
規約：像の零対象を用いる厳密等号。使われ方：点つき実現写像。 -/
lemma diagonalSPostcomp_zeroVertex {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f) (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    (diagonalSPostcomp f hf).app (Opposite.op ⦋0⦌) (coreSConstructionZeroVertex 0 z hz) =
      coreSConstructionZeroVertex 0 (f.app (Opposite.op ⦋0⦌) z) (hf.1 z hz) := by
  apply Subtype.ext
  exact sPostcomp_zeroVertex 0 f hf z hz

end SerrePositivity.KST.SConstruction
