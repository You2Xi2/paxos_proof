module Network {

datatype Packet<IdType, MessageType> = Packet(src:IdType, dst:IdType, msg:MessageType)

datatype EnvStep<IdType, MessageType> = 
    IoStep(actor:IdType, recvIo:Packet<IdType, MessageType>, sendIos:seq<Packet<IdType, MessageType>>)

datatype Environment<IdType(==), MessageType(==)> = Env(
        sentPackets:set<Packet<IdType, MessageType>>,
        recvdPackets:set<Packet<IdType, MessageType>>,
        nextStep:EnvStep<IdType, MessageType>
    )
}