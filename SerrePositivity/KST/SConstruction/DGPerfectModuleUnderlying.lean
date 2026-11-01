module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

/-!
概要：実 Perf 値 dg 関手を、同じ Hom 鎖写像を持つ実加群値関手として読む。
方針：充満 dg 部分圏の対象を忘れ、元の map・単位・合成証拠をそのまま使う。
規約：包含との合成に現れる恒等鎖写像を正規化に任せない。
使われ方：大きな実逆回転関手の全自然性を、元 Hom の表示のまま利用する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type w} [DGCategory R P]

/-- 概要：実 Perf 値関手の同じ全 Hom を持つ実加群値関手。
方針：元の三つの構造欄を直接保持する。
規約：射を恒等と合成して変更しない。使われ方：全 Hom 自然性の軽い型照合。 -/
def dgPerfectModuleUnderlying (F : DGFunctor R P (PerfectDGModule R E)) :
    DGFunctor R P (RightModule R E) where
  obj x := (F.obj x).val
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp
end SerrePositivity.KST.SConstruction
