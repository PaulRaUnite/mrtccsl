(
    (Variable(name ca)(writes(controller.end))(reads(actuator.start)))
    (Queue(name ss)(writes(sensor.start))(reads(sensor.end)))
    (Queue(name sc)(writes(sensor.end))(reads(controller.start)))
    (Queue(name cc)(writes(controller.start))(reads(controller.end)))
    (Queue(name aa)(writes(actuator.start))(reads(actuator.end)))
    
    (Inject(at sensor.start)(colors(chain1)))
    (Probe(name chain1probe)(expect_all(chain1))(at actuator.end))
)