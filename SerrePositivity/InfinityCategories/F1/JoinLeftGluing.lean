module

public import SerrePositivity.InfinityCategories.Core.JoinFunctor

/-!
概要：join の左因子に関する二辺の貼り合わせ。
方針：部分複体の和と交わりを join に移し、内ホーンの pushout を写す。
規約：右因子を固定し、左因子を図式として変化させる。
使われ方：Kerodon Proposition 5.2.5.1、合成可能な transport の錐の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右因子を固定した join は左因子の射に関して関手。
方針：joinMap の右成分に恒等射を入れる。
規約：固定した右因子は B。
使われ方：Kerodon §4.3.3、Proposition 5.2.5.1 の内ホーンの貼り合わせ。 -/
def joinLeftFunctor (B : SSet.{u}) : SSet.{u} ⥤ SSet.{u} where
  obj A := join A B
  map f := joinMap f (𝟙 B)
  map_id A := joinMap_id A B
  map_comp f g := by simpa only [Category.comp_id] using joinMap_comp f g (𝟙 B) (𝟙 B)

/-- 概要：左因子の部分複体の交わりは join の交わりに写る。
方針：補った次数での左単体の所属を比較する。
規約：右因子 B は共通。
使われ方：Kerodon §4.3.3、合成の三角形の錐の貼り合わせ。 -/
lemma joinSubcomplexLeft_inf (B : SSet.{u}) {A : SSet.{u}} (A₀ A₁ : A.Subcomplex) :
    joinSubcomplexLeft (A₀ ⊓ A₁) B = joinSubcomplexLeft A₀ B ⊓ joinSubcomplexLeft A₁ B := by
  ext ⟨⟨n⟩⟩ s
  change (s ∈ (joinSubcomplexLeft (A₀ ⊓ A₁) B).obj _) ↔
    s ∈ (joinSubcomplexLeft A₀ B).obj _ ∧ s ∈ (joinSubcomplexLeft A₁ B).obj _
  rw [Join.mem_joinSubcomplexLeft, Join.mem_joinSubcomplexLeft,
    Join.mem_joinSubcomplexLeft, Join.augMem_inf]

/-- 概要：左因子の部分複体の和は join の和に写る。
方針：補った次数での左単体の所属を比較する。
規約：二項の和の保存だけを主張する。
使われ方：Kerodon §4.3.3、合成の三角形の錐の貼り合わせ。 -/
lemma joinSubcomplexLeft_sup (B : SSet.{u}) {A : SSet.{u}} (A₀ A₁ : A.Subcomplex) :
    joinSubcomplexLeft (A₀ ⊔ A₁) B = joinSubcomplexLeft A₀ B ⊔ joinSubcomplexLeft A₁ B := by
  ext ⟨⟨n⟩⟩ s
  change (s ∈ (joinSubcomplexLeft (A₀ ⊔ A₁) B).obj _) ↔
    s ∈ (joinSubcomplexLeft A₀ B).obj _ ∨ s ∈ (joinSubcomplexLeft A₁ B).obj _
  rw [Join.mem_joinSubcomplexLeft, Join.mem_joinSubcomplexLeft,
    Join.mem_joinSubcomplexLeft, Join.augMem_sup]

/-- 概要：左因子の双カルテジアンな部分複体の正方形は join の同じ正方形に写る。
方針：和と交わりの保存を組み合わせる。
規約：右因子 B を固定する。
使われ方：Kerodon §4.3.3、内ホーンの二辺への分解。 -/
lemma joinSubcomplexLeft_bicartSq (B : SSet.{u}) {A : SSet.{u}}
    {A₀ A₁ A₂ A₃ : A.Subcomplex} (h : Subcomplex.BicartSq A₀ A₁ A₂ A₃) :
    Subcomplex.BicartSq (joinSubcomplexLeft A₀ B) (joinSubcomplexLeft A₁ B)
      (joinSubcomplexLeft A₂ B) (joinSubcomplexLeft A₃ B) where
  sup_eq := by rw [← joinSubcomplexLeft_sup, h.sup_eq]
  inf_eq := by rw [← joinSubcomplexLeft_inf, h.inf_eq]

/-- 概要：左因子の部分複体の表示同型から join の像の表示同型を作る。
方針：join 関手の同型と部分複体の像の同型を合成する。
規約：e は C から A₀ への同型。
使われ方：Kerodon §4.3.3、内ホーンの標準表示への移行。 -/
noncomputable def joinLeftSubcomplexIso (B : SSet.{u}) {A C : SSet.{u}}
    (A₀ : A.Subcomplex) (e : C ≅ (A₀ : SSet.{u})) :
    join C B ≅ (joinSubcomplexLeft A₀ B : SSet.{u}) :=
  (joinLeftFunctor B).mapIso e ≪≫ joinSubcomplexLeftIso A₀ B

/-- 概要：左因子の部分複体の join の表示同型は周囲への包含と可換。
方針：像への包含と joinMap の合成則を使う。
規約：右成分の射は恒等。
使われ方：Kerodon §4.3.3、pushout の比較。 -/
lemma joinLeftSubcomplexIso_hom_ι (B : SSet.{u}) {A C : SSet.{u}}
    (A₀ : A.Subcomplex) (e : C ≅ (A₀ : SSet.{u})) :
    (joinLeftSubcomplexIso B A₀ e).hom ≫ (joinSubcomplexLeft A₀ B).ι =
      joinMap (e.hom ≫ A₀.ι) (𝟙 B) := by
  rw [joinLeftSubcomplexIso, Iso.trans_hom, Category.assoc, joinSubcomplexLeftIso_hom_ι]
  change joinMap e.hom (𝟙 B) ≫ joinMap A₀.ι (𝟙 B) = _
  rw [← joinMap_comp, Category.comp_id]

/-- 概要：合成可能な二辺との join を共通の頂点との join で貼ると内ホーンとの join になる。
方針：内ホーンの部分複体の pushout を join の左因子へ移す。
規約：共通の頂点は二単体の一番目の頂点。
使われ方：Kerodon Proposition 5.2.5.1、二つの transport の錐の貼り合わせ。 -/
lemma joinLeft_horn₂₁_isPushout (A : SSet.{u}) :
    IsPushout (joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A))
      (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A))
      (joinMap horn₂₁.ι₀₁ (𝟙 A)) (joinMap horn₂₁.ι₁₂ (𝟙 A)) := by
  let hs := joinSubcomplexLeft_bicartSq A horn₂₁.sq
  apply hs.isPushout.of_iso'
    (joinLeftSubcomplexIso A (stdSimplex.face {1}) (stdSimplex.faceSingletonIso 1))
    (joinLeftSubcomplexIso A (stdSimplex.face {0, 1}) (stdSimplex.facePairIso 0 1 (by decide)))
    (joinLeftSubcomplexIso A (stdSimplex.face {1, 2}) (stdSimplex.facePairIso 1 2 (by decide)))
    (joinSubcomplexLeftIso (horn 2 1) A)
  · apply (cancel_mono (joinSubcomplexLeft (stdSimplex.face {0, 1}) A).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinLeftSubcomplexIso_hom_ι]
    rw [← joinMap_comp, Category.comp_id]
    apply congrArg (fun f ↦ joinMap f (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide
  · apply (cancel_mono (joinSubcomplexLeft (stdSimplex.face {1, 2}) A).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinLeftSubcomplexIso_hom_ι]
    rw [← joinMap_comp, Category.comp_id]
    apply congrArg (fun f ↦ joinMap f (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide
  · apply (cancel_mono (joinSubcomplexLeft (horn 2 1) A).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinLeftSubcomplexIso_hom_ι,
      joinSubcomplexLeftIso_hom_ι]
    rw [← joinMap_comp, Category.comp_id]
    apply congrArg (fun f ↦ joinMap f (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide
  · apply (cancel_mono (joinSubcomplexLeft (horn 2 1) A).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, joinLeftSubcomplexIso_hom_ι,
      joinSubcomplexLeftIso_hom_ι]
    rw [← joinMap_comp, Category.comp_id]
    apply congrArg (fun f ↦ joinMap f (𝟙 A))
    apply SSet.yonedaEquiv.injective
    decide

end SerrePositivity.InfinityCategories
